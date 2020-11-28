import abc
import re
from io import StringIO


class MinizincTranslator:

    def __init__(self, out_file):
        self.out_file = out_file

    def _input_preprocessing(self, text_io: StringIO):
        new_lines = []
        declaration_set_id = set()
        for line in text_io.readlines():
            if not line.startswith(";"):
                line = re.sub(r";.*", "", line)
                if "assert-soft" in line:
                    if ":id " in line:
                        new_var = line.split(":id")[-1].strip().replace(")", "")
                    else:
                        new_var = "I"
                    if new_var not in declaration_set_id:
                        new_lines.append("\n(declare-fun " + new_var + " () %s)\n" % (self.asoft_var_type))
                        declaration_set_id.add(new_var)
                if "(set-option" in line:
                    line = re.sub(":", " : ", line)
                new_lines.append(line)
        return StringIO("\n".join(new_lines))

    def _parse_stack(self, commands, out_file):
        current_stack = [[]]
        file_index = 1
        for cmd in commands:
            if cmd.name == 'push':
                npush = cmd.args[0] if cmd.args else 1
                current_stack.extend([[] for _ in range(npush)])
            elif cmd.name == 'pop':
                npop = cmd.args[0] if cmd.args else 1
                del current_stack[-npop:]
            elif cmd.name == 'check-sat':
                new_out_file = self.out_file.replace(".mzn", "_" + str(
                    file_index) + ".mzn")
                with open(new_out_file, "w") as ffile:
                    self.write_stack(current_stack, ffile)
                file_index += 1
            else:
                current_stack[-1].append(cmd)

    @abc.abstractmethod
    def parse(self, text_buf):
        '''Main function responsible to generate the minizinc output, the input is a buffered text'''
        pass

    @abc.abstractmethod
    def write_stack(self, current_stack, file_pointer):
        pass

class CommandsStack:

    def __init__(self):
        self._variables = dict()
        self._commands = []
        self._asserts = []
        self._asserts_soft = []

    @property
    def commands(self):
        return self._commands

    @property
    def asserts(self):
        return self._asserts

    @property
    def asserts_soft(self):
        return self._asserts_soft

    @property
    def variables(self):
        return self._variables






