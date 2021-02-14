from pysmt.minizinc.translator import MinizincTranslator, CommandsStack
from pysmt.smtlib import parser
import itertools

class OmtCommandsStack(CommandsStack):

    PRIORITY_OPTION = frozenset(("box", "lex"))
    def __init__(self):
        super().__init__()
        self._priority_option = "box"

    @property
    def priority_option(self):
        return self._priority_option

    @property.setter
    def priority_option(self, option_value):
        if option_value not in self.PRIORITY_OPTION:
            raise ValueError("The current optimization option is not currently supported")
        self._priority_option = option_value

class OmtToMzn(MinizincTranslator):

    def __init__(self, out_file):
        super().__init__(out_file)

    def translate(self, lines):
        new_lines = self._input_preprocessing(lines)
        script = parser.get_script(new_lines)
        self._parse_stack(script.commands, self.out_file)

    def write_stack(self, stack, out_file):
        """ write out to the minizinc file the input stack """
        command_stack = OmtCommandsStack()
        for el in itertools.chain(*stack):
            if el.name == 'declare-fun' and len(el.args) == 1:
                command_stack.variables[str(el.args[0])] = [el.args[0].get_type()]
            elif el.name == 'assert':
                command_stack.asserts.append(el.args)
            elif el.name == 'assert-soft':
                command_stack.asserts_soft.append(el.args)
            elif el.name == 'set-option' and el.args[1] == 'opt.priority':  # keep the last one
                command_stack.priority_option = el.args[-1]
            elif el.name == 'maximize' or el.name == 'minimize':
                command_stack.commands.append((el.name, el.args))
        var_dict = self.modify_type_assert_soft_var(command_stack.asserts_soft, command_stack.variables)
        var_dict = self.add_id_variables_opt(command_stack.commands, command_stack.variables)

        if not command_stack.commands:  # satisfiability problem
            self.write_sat_stack(command_stack, out_file)
        else:
            if command_stack.priority_option == 'lex':  # multi optimization problem with lexicographic approach
                self.write_lex_stack(command_stack, out_file)
            else:  # multi optimization problem with boxed approach (default one)
                self.write_box_stack(command_stack, out_file)

    def write_box_stack(self, command_stack, out_file):
        pass

    def write_lex_stack(self, command_stack, out_file):
        pass

