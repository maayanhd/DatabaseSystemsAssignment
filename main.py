import copy
import random

rules_menu = {'1': "4", '2': "4a", '3': "5a", '5': "6", '6': "11b"}
num_to_opt_rules_menu = {1: "4", 2: "4a", 3: "5a", 4: "6", 5: "11b"}
list_of_expressions_lists = []


def tester_menu():
    menu = {'1': "Part 1", '2': "Part 2", '3': "Part 3"}
    options = menu.keys()
    print("please choose an option:")
    for entry in sorted(options):
        print(entry + ". " + menu[entry])
    option_num = input()
    is_option_valid = False

    while not is_option_valid:
        if option_num == '1' or option_num == '2':
            optimize_query(menu[option_num])
            is_option_valid = True
        elif option_num == '3':
            '''implementation part 3'''
            estimateQueryPlans()
            is_option_valid = True
        else:
            print("illegal option, must an existing option number, please try again!")


def estimateQueryPlans():
    '''YET TO BE IMPLEENTED'''

def optimize_query(mode):
    expression_list = create_expression_list()

    if mode == "Part 1":
        optimization_rule = get_optimization_rule()
        optimized_exp_list = optimize_expr_by_opt_rule(expression_list.copy(), optimization_rule.strip())
    elif mode == "Part 2":
        '''Making 4 copies of Logical Queries Expressions '''
        for i in range(0, 4):
            list_of_expressions_lists.append(copy.deepcopy(expression_list))
        for i in range(0, 4):
            for itr in range(0, 10):
                print(f"Iteration {itr + 1} out of 10:")
                optimization_rule = num_to_opt_rules_menu[random.randint(1, 6)]
                list_of_expressions_lists[i] = optimize_expr_by_opt_rule(list_of_expressions_lists[i],
                                                                         optimization_rule.strip())
                # '''list_of_expressions_lists[i] = optimize_expr_by_opt_rule(list_of_expressions_lists[i], '4')'''
            print(f"just finished optimizing logical query plan {i + 1}\n")

        '''Printing Optimized Expressions'''
        print("\n", end="")
        for i in range(0, 4):
            print(f"optimized expression number {i + 1}:")
            print_expression_list(list_of_expressions_lists[i])
            print("\n", end="")

def optimize_expr_by_opt_rule(expression_list, optimization_rule):
    optimized_expression_list = []
    if optimization_rule == '4':
        optimized_expression_list = apply_rule_4(expression_list)
    elif optimization_rule == '4a':
        optimized_expression_list = apply_rule_4a(expression_list)
    elif optimization_rule == '5a':
        optimized_expression_list = apply_rule_5a(expression_list)
    elif optimization_rule == '6':
        optimized_expression_list = apply_rule_6(expression_list)
    elif optimization_rule == '11b':
        optimized_expression_list = apply_rule_11b(expression_list)

    return optimized_expression_list


def apply_rule_4(expression_list):
    print("Applying optimization rule 4 ...")
    for ind, op in enumerate(expression_list):
        if isinstance(op, Sigma):
            partitioned_and_index = get_partitioned_and_index_aux(op.predicate)
            if partitioned_and_index != -1:
                expression_list = update_expression_rule_4(partitioned_and_index, ind, expression_list)
                break

    print_expression_list(expression_list)
    print("\n\n", end="")
    return expression_list


def update_expression_rule_4(and_str_index, sigma_list_index, expression_list):
    predicate = expression_list[sigma_list_index].predicate
    left_sigma = Sigma(predicate[:and_str_index].strip())
    expression_list[sigma_list_index].predicate = predicate[and_str_index + 3:].strip()
    expression_list.insert(sigma_list_index, left_sigma)

    return expression_list


def apply_rule_4a(expression_list):
    return expression_list


def apply_rule_5a(expression_list):
    optimized_exp_list = []
    return optimized_exp_list


def apply_rule_6(expression_list):
    optimized_exp_list = []
    return optimized_exp_list


def apply_rule_11b():
    optimized_exp_list = []
    return optimized_exp_list


def get_optimization_rule():
    str_rule = ""
    while True:
        options = rules_menu.keys()

        for entry in sorted(options):
            print(entry + ". " + rules_menu[entry])
        selection = input("Please Choose one option:")

        if selection == '1':
            str_rule += rules_menu['1']
            break
        elif selection == '2':
            str_rule += rules_menu['2']
            break
        elif selection == '3':
            str_rule += rules_menu['3']
            break
        elif selection == '4':
            str_rule += rules_menu['4']
            break
        elif selection == '5':
            str_rule += rules_menu['5']
            break
        elif selection == '6':
            str_rule += rules_menu['6']
            break
        else:
            print("Unknown Option Selected!")
            break

    return str_rule


def create_expression_list():
    print("Enter a SQL query")
    query_str = input()
    select_idx = query_str.find("SELECT")
    from_idx = query_str.find("FROM")
    where_idx = query_str.find("WHERE")

    select_str = query_str[select_idx + 6: from_idx].strip()
    if select_str.split(" ")[0] == "DISTINCT":
        attribute_list_str = select_str[8:]
    else:
        attribute_list_str = select_str

    table_list_str = query_str[from_idx + 4: where_idx].strip()

    if query_str[-1] == ";":
        condition_str = query_str[where_idx + 5:-1].strip()
    else:
        condition_str = query_str[where_idx + 5:].strip()

    pi_elem = Pi(attribute_list_str.split(","))
    sigma_elem = Sigma(condition_str)
    cartesian_elem = Cartesian(table_list_str.split(","))
    expression_list = [pi_elem, sigma_elem, cartesian_elem]

    return expression_list


def print_expression_list(expression_list):
    if len(expression_list) == 1:
        print(expression_list[0].__str__(), end="")
    else:
        print(expression_list[0].__str__() + "(", end="")
        print_expression_list(expression_list[1:])
        print(")", end="")


def get_partitioned_and_index_aux(cond_str):
    if is_simple_cond(cond_str):
        return -1
    elif cond_str[0] == "(" and cond_str[-1] == ")" and is_condition(cond_str[1:-1]):
        return get_partitioned_and_index(cond_str[1:-1])
    elif cond_str.count("AND"):
        return get_partitioned_and_index(cond_str)
    else:
        return -1


def get_partitioned_and_index(cond_str):
    log_op_indexes = [i for i in range(len(cond_str)) if cond_str.startswith("AND", i)]
    for i in log_op_indexes:
        if cond_str[i:i + 3] == "AND":
            if is_condition(cond_str[0:i].strip()) and is_condition(cond_str[i + 3:].strip()):
                return i

    '''If there is no AND'''
    return -1


def is_condition(cond_str):
    if is_simple_cond(cond_str):
        return True
    elif cond_str[0] == "(" and cond_str[-1] == ")" and is_condition(cond_str[1:-1]):
        return True

    elif cond_str.count("AND") or cond_str.count("OR"):

        log_op_indexes = [i for i in range(len(cond_str)) if
                          cond_str.startswith("AND", i) or cond_str.startswith("OR", i)]

        for i in log_op_indexes:
            if cond_str[i:i + 3] == "AND":
                if is_condition(cond_str[0:i].strip()) and is_condition(cond_str[i + 3:].strip()):
                    return True
            else:
                if is_condition(cond_str[0:i].strip()) and is_condition(cond_str[i + 2:].strip()):
                    return True

        return False

    else:
        return False


def is_simple_cond(simple_cond_str):
    two_char_ops = [(simple_cond_str.find('<='), simple_cond_str.count('<=')), (simple_cond_str.find('>=')
                                                                                , simple_cond_str.count('>=')),
                    (simple_cond_str.find('<>'), simple_cond_str.count('<>'))]
    single_char_ops = [(simple_cond_str.find('<'), simple_cond_str.count('<')), (simple_cond_str.find('>'),
                                                                                 simple_cond_str.count('>')),
                       (simple_cond_str.find('='), simple_cond_str.count('='))]

    op_idx = -1
    op_count = 0
    for op in two_char_ops:
        if op[1] == 1:
            op_idx = op[0]
            op_count += 1
        elif op[1] > 1:
            ''' two operators '''
            return False

    if op_count == 0:
        ''' There is no two character operators'''
        for op in single_char_ops:
            if op[1] == 1:
                op_idx = op[0]
                op_count += 1
            elif op[1] > 1:
                ''' two operators '''
                return False

        if op_count == 0:
            ''' There is no operators in the string'''
            return False
        elif op_count == 1:
            ''' single character operator found '''
            return is_constant(simple_cond_str[0:op_idx].strip()) and is_constant(simple_cond_str[op_idx + 1:].strip()) \
                   and is_matching_types(simple_cond_str[0:op_idx].strip(), simple_cond_str[op_idx + 1:].strip())
        else:
            ''' more than 1 operator '''
            return False

    elif op_count == 1:
        ''' two characters operator found'''
        return is_constant(simple_cond_str[0:op_idx].strip()) and is_constant(simple_cond_str[op_idx + 2:].strip()) \
               and is_matching_types(simple_cond_str[0:op_idx].strip(), simple_cond_str[op_idx + 1:].strip())
    else:
        '''more than 1 operator'''
        return False


def is_matching_types(left_constant, right_constant):
    return get_constant_type(left_constant) == get_constant_type(right_constant)


def get_constant_type(constant):
    temp_constant = constant.split(".")
    if is_a_string(constant):
        return "STRING"
    elif len(temp_constant) == 2:

        if temp_constant[1] == "A" or temp_constant[1] == 'B' or temp_constant[1] == 'C' or temp_constant[1] == 'D' \
                or temp_constant[1] == 'E' or temp_constant[1] == 'F' or temp_constant[1] == 'G' \
                or temp_constant[1] == 'H' or temp_constant[1] == 'I':
            return "INTEGER"
    else:
        return "INTEGER"


def is_constant(constant_str):
    if constant_str and (constant_str.isnumeric() or is_a_string(constant_str) or is_attribute(constant_str)):
        return True
    else:
        return False


def is_attribute(attribute):
    temp_list = attribute.split(".")
    if len(temp_list) != 2:
        return False
    else:
        table_name = temp_list[0]
        attribute_name = temp_list[1]

        if table_name == "R":
            return attribute_name.strip() == "A" or attribute_name.strip() == "B" or attribute_name.strip() == "C" or \
                   attribute_name.strip() == "D" or attribute_name.strip() == "E"
        elif table_name == "S":
            return attribute_name.strip() == "D" or attribute_name.strip() == "E" or attribute_name.strip() == "F" or \
                   attribute_name.strip() == "G" or attribute_name.strip() == "H" or attribute_name.strip() == "I"
        else:
            return False


def is_a_string(sql_str):
    return (sql_str[0] == '"' and sql_str[-1] == '"') or (sql_str[0] == "'" and sql_str[-1] == "'") or (
            sql_str[0] == "’" and sql_str[-1] == "’") or (sql_str[0] == "`" and sql_str[-1] == "`")


class Pi:
    def __init__(self, att_list):
        self.att_list = att_list

    def __str__(self):
        representing_str = "PI["
        for col in self.att_list:
            representing_str += (col + ",")
        '''removing the last "," '''
        representing_str = representing_str[0:-1]
        representing_str += "]"

        return representing_str


class Sigma:
    def __init__(self, predicate):
        self.predicate = predicate

    def __str__(self):
        representing_str = "SIGMA["
        representing_str += (self.predicate + "]")

        return representing_str


class Cartesian:
    def __init__(self, table_list):
        self.table_list = table_list

    def __str__(self):
        representing_str = "CARTESIAN("
        for table in self.table_list:
            representing_str += (table + ",")
        '''removing the last "," '''
        representing_str = representing_str[0:-1]
        representing_str += ")"

        return representing_str


class Njoin:
    def __init__(self, table_list):
        self.table_list = table_list

    def __str__(self):
        representing_str = "NJOIN("
        for table in self.table_list:
            representing_str += (table + ",")
        '''removing the last "," '''
        representing_str = representing_str[0:-1]
        representing_str += ")"

        return representing_str


class Tjoin:
    def __init__(self, predicate, table_list):
        self.predicate = predicate
        self.table_list = table_list

    def __str__(self):
        representing_str = "[TJOIN"
        representing_str += (self.predicate + "]")
        for table in self.table_list:
            representing_str += ("(" + table + ",")
        '''removing the last "," '''
        representing_str = representing_str[0:-1]
        representing_str += ")"

        return representing_str

class Schema:
    def __init__(self, n_rows, n_width):
        self.n_rows = n_rows
        self.n_width = n_width


if __name__ == '__main__':
    tester_menu()
