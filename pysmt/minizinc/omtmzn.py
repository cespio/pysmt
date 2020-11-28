from pysmt.minizinc.translator import MinizincTranslator, CommandsStack
from pysmt.smtlib import parser
import itertools

class OmtCommandsStack(CommandsStack):

    def __init__(self):
        super().__init__()
        self._priority_option = "box"

    @property
    def priority_option(self):
        return self._priority_option

    @property.setter
    def priority_option(self, option_value):
        self._priority_option = option_value

class OmtToMzn(MinizincTranslator):

    def __init__(self, out_file):
        super().__init__(out_file)

    def parse(self, lines):
        new_lines = self._input_preprocessing(lines)
        script = parser.get_script(new_lines)
        self._parse_stack(script.commands, self.out_file)

    def write_stack(self, stack, out_file):
        """ write minizinc file related to each stack """
        command_stack = OmtCommandsStack()
        var_dict = {}
        asserts_list = []
        asserts_soft_list = []
        commands_list = []  # maximize/minimize
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
                commands_list.append((el.name, el.args))
        var_dict = self.modify_type_assert_soft_var(asserts_soft_list, var_dict)
        var_dict = self.add_id_variables_opt(commands_list, var_dict)
        print("Finished to write the stack")
        if len(commands_list) == 0:
            self.write_stack_simple(var_dict, asserts_list, asserts_soft_list, out_file)
        else:
            if set_priority_option == 'lex':  # lexicographic order
                self.write_stack_lex(var_dict, asserts_list, asserts_soft_list, commands_list, out_file)
            else:  # box-  also the default one
                self.write_stack_box(var_dict, asserts_list, asserts_soft_list, commands_list, out_file)
