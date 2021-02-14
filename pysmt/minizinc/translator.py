import abc
import re
import logging
from pysmt.environment import get_env
from pysmt.minizinc.printers import MZNPrinter
from io import StringIO


class MinizincTranslator:

    def __init__(self, out_file, daggify=True, two_fathers=True, big_and=False, max_int_bit_size=8):
        self.out_file = out_file
        self._daggify = daggify
        self._big_and = big_and
        self._serializer = MZNPrinter(two_fathers, max_int_bit_size)
        self._logger = logging.getLogger(__name__)
        self._logger.setLevel(logging.INFO)

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
                        new_lines.append("\n(declare-fun " + new_var + " () %s)\n" % (self.asoft_var_type))  # TODO asoft_var_type
                        declaration_set_id.add(new_var)
                if "(set-option" in line:
                    line = re.sub(":", " : ", line)
                new_lines.append(line)
        return StringIO("\n".join(new_lines))

    def _parse_stack(self, commands):
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
    def translate(self, text_buf):
        """Main function responsible to generate the minizinc output, the input is a buffered text"""
        pass

    @abc.abstractmethod
    def write_stack(self, current_stack, file_pointer):
        pass

    def write_sat_stack(self, command_stack, out_file):
        with open(out_file, "w") as file_out:
            self._logger.info("writing variables...")
            self._write_variables_lists(command_stack.variables, file_out)
            self._logger.info("writing assertions...")
            self.write_assertions(command_stack.asserts, file_out)
            self._logger.info("writing asserts-soft...")
            self.write_assertions_soft(command_stack.asserts_soft, file_out)
            self._logger.info("writing satisfy...")
            file_out.write("solve satisfy;\n")

    @staticmethod
    def _write_variables_lists(variables, out_file):
        """ Writes the variables declaration in minizinc """
        for var_name in variables:
            # In MiniZinc if no domain is specified there can be problems with some solvers
            bv_match = re.match(r"BV{([0-9]+)}", str(variables[var_name][0]))
            if bv_match:
                upper_bound = pow(2, int(bv_match.groups(0)[0])) - 1
                out_file.write(f"var 0..{upper_bound}:{var_name};\n")
            elif "Real" in str(variables[var_name][0]):
                out_file.write(f"var -3.402823e+38..3.402823e+38 : {var_name};\n")
            else:
                var_type = variables[var_name][0].lower()
                out_file.write(f"var {var_type}:{var_name};\n")

    def write_assertions(self, asserts_list, file_out):
        """ Write the assertion to the output file """
        if self._big_and:
            mgr = get_env()._formula_manager  # TODO propose a better usage of the formula manager and env stack
            big_and = asserts_list[0][0]
            for el in asserts_list[1:]:
                tmp = el[0] if type(el) is list else el
                big_and = mgr.And(big_and, tmp)
            self._serializer.serialize(big_and, output_file=file_out)
        else:
            for el in asserts_list:
                if type(el) is list:
                    el = el[0]
                self._serializer.serialize(el, output_file=file_out)

    def write_assertions_soft(self, asserts_soft_list, file_out):
        """
            Writing the soft-assertions list
            for each group of assertion with the same ID add its related group of constraint
            (assert-soft a :weight expr1 :id goal)
            (assert-soft b :weight expr2 :id goal)
            -----
            (constraint bv_goal_1=a)
            (constraint bv_goal_2=b)
            (constraint bv_goal = not(a)*expr1 + not(b)*expr2)
        """
        cost_variables_set = set([assert_soft[-1] for assert_soft in asserts_soft_list])  # assert_soft[-1] = id name of the var
        var_index = {name: 0 for name in cost_variables_set}
        var_weight = {}
        for assert_soft in asserts_soft_list:
            cost_variable_index_name = f"{assert_soft[-1]}_{var_index[assert_soft[-1]]}"
            assert_soft_expr_serialized = self._serializer.serialize(assert_soft[0])

            file_out.write(f"var bool: {cost_variable_index_name};\n")
            file_out.write(f"constraint ({cost_variable_index_name} = {assert_soft_expr_serialized});\n")
            var_weight[f"{cost_variable_index_name}"] = self._serializer.serialize(assert_soft[1], daggify=False)
            var_index[assert_soft[-1]] += 1

        for cost_variable in cost_variables_set:
            file_out.write(f"constraint ({cost_variable}=")
            str_ap = []
            for k in var_weight:
                if cost_variable in k:
                    str_ap.append(f"not({k})*({str(var_weight[k])})")
            file_out.write("+".join(str_ap) + ");\n")

            # computing the bound for the assert-soft id variables
            negative_weights = []
            positive_weights = []
            for k in var_weight:
                if cost_variable in k and eval(var_weight[k]) < 0:
                    negative_weights.append(f"({str(var_weight[k])}")
                elif cost_variable in k and eval(var_weight[k]) >= 0:
                    positive_weights.append(f"({str(var_weight[k])}")
            file_out.write("constraint (")
            lower_bound = "+".join(negative_weights) if negative_weights else "0"
            upper_bound = "+".join(positive_weights) if positive_weights else "0"
            file_out.write(f" ({lower_bound}) <= {cost_variable} /\\ {cost_variable} <= ({upper_bound}));\n")

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
