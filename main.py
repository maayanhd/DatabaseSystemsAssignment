import copy
import random
import math

rules_menu = {'1': "4", '2': "4a", '3': "5a", '4': "6", '5': "6a", '6': '11b'}
num_to_opt_rules_menu = {1: "4", 2: "4a", 3: "5a", 4: "6", 5: "6a", 6: "11b"}
list_of_expressions_lists = []
lqp_state = []

''' auxiliary for parsing conditions using a modification of is_condition method from the previous exercise '''
parsed_predicate_att_list = []


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
            expression_list = create_expression_list()
            optimize_query(menu[option_num], expression_list)
            is_option_valid = True
        elif option_num == '3':
            estimate_query_plans()
            is_option_valid = True
        else:
            print("illegal option, must an existing option number, please try again!")
            option_num = input()
            is_option_valid = False


def estimate_query_plans():
    expression_list = adjust_expression_list_by_file(create_expression_list())
    list_of_expressions = optimize_query("Part 2", expression_list)

    for exp in list_of_expressions:
        print("\n")
        print("Size estimation of: ", end="\n")
        print_expression_list(exp)
        print("\n")
        exp_list = copy.deepcopy(exp)
        exp_list.reverse()
        estimate_query_plan(exp_list)


def estimate_query_plan(reversed_exp_list):
    """ in order to avoid compilation errors, creating temp initial Schemas, that will be initialized first by design (design by contract) """

    left_schema_res = Schema("initial")
    right_schema_res = Schema("initial")
    res_schema = Schema("initial")

    for i, elem in enumerate(reversed_exp_list):
        if isinstance(elem, Pi):
            res_schema.__copy__(estimate_pi(elem, res_schema))
        elif isinstance(elem, Sigma):
            res_schema.__copy__(estimate_sigma(elem, res_schema))
        elif isinstance(elem, Cartesian):
            res_schema.__copy__(estimate_cartesian(left_schema_res, right_schema_res))
        elif isinstance(elem, Njoin):
            res_schema.__copy__(estimate_njoin(left_schema_res, right_schema_res))
        elif isinstance(elem, Pair):
            reversed_exp_list[i].left_lst.reverse()
            reversed_exp_list[i].right_lst.reverse()
            left_schema_res.__copy__(estimate_query_plan(reversed_exp_list[i].left_lst))
            right_schema_res.__copy__(estimate_query_plan(reversed_exp_list[i].right_lst))
        elif isinstance(elem, Schema):
            res_schema.__copy__(elem)

    return res_schema


def estimate_pi(pi_operator, processed_schema):
    print(pi_operator.__str__())
    print("input: " + processed_schema.get_estimation_stat_str())

    res_att_to_v = {}
    res_att_to_size = {}
    for att in pi_operator.att_list:
        res_att_to_v[att] = processed_schema.att_to_v[att]
        res_att_to_size[att] = processed_schema.att_to_size[att]

    res_schema = Schema("Scheme" + str(processed_schema.name_counter + 1), processed_schema.n_rows, \
                        pi_operator.att_list, res_att_to_v, res_att_to_size, processed_schema.name_counter + 1)

    print("output: " + res_schema.get_estimation_stat_str() + "\n")

    return res_schema


def estimate_cartesian(schema_1, schema_2):
    print("CARTESIAN")
    print("input: " + schema_1.get_estimation_stat_str() + " " + schema_2.get_estimation_stat_str())

    new_att_list = copy.deepcopy(schema_1.att_list)
    new_att_list.extend(copy.deepcopy(schema_2.att_list))
    new_att_to_v = copy.deepcopy(schema_1.att_to_v)
    new_att_to_v.update(copy.deepcopy(schema_2.att_to_v))
    new_att_to_size = copy.deepcopy(schema_1.att_to_size)
    new_att_to_size.update(copy.deepcopy(schema_2.att_to_size))

    res_schema = Schema("Scheme" + str(schema_1.name_counter + schema_2.name_counter + 1), \
                        schema_1.n_rows * schema_2.n_rows, new_att_list, \
                        new_att_to_v, new_att_to_size, schema_1.name_counter + schema_2.name_counter + 1)

    print("output: " + res_schema.get_estimation_stat_str() + "\n")

    return res_schema


def apply_rule_4(expression_list):
    lqp_state.append("4")
    ind_of_pair = None
    new_exp_list = copy.deepcopy(expression_list)
    for ind, op in enumerate(expression_list):
        if isinstance(op, Sigma):
            partitioned_and_index = get_partitioned_and_index_aux(op.predicate)
            if partitioned_and_index != -1:
                new_exp_list = update_expression_rule_4(partitioned_and_index, ind, new_exp_list)
                break
        if isinstance(op, Pair):
            ind_of_pair = ind

    if ind_of_pair:
        left_list = apply_rule_4(expression_list[ind_of_pair].left_lst)
        if left_list == expression_list[ind_of_pair].left_lst:
            new_exp_list[ind_of_pair].right_lst = apply_rule_4(expression_list[ind_of_pair].right_lst)
        else:
            new_exp_list[ind_of_pair].left_lst = left_list

    lqp_state.clear()
    return new_exp_list


def update_expression_rule_4(and_str_index, sigma_list_index, expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    predicate = expression_list[sigma_list_index].predicate
    left_sigma = Sigma(predicate[:and_str_index].strip())
    new_exp_list[sigma_list_index].predicate = predicate[and_str_index + 3:].strip()
    new_exp_list.insert(sigma_list_index, left_sigma)

    return new_exp_list

def remove_unnecessary_parenthesis_in_sigma_list(sigma_list):

    temp_list = copy.deepcopy(sigma_list)
    for i,sigma in enumerate(sigma_list):
        predicate = removeAllOuterParenthesis(sigma.predicate).strip()
        if predicate[0] == "(" and predicate[-1] == ")" and is_condition(predicate[1:-1]):
            temp_list[i].predicate = predicate[1:-1]


    return temp_list

def estimate_sigma(sigma_op, processed_schema):
    print(sigma_op.__str__())
    print("input: " + processed_schema.get_estimation_stat_str())
    sigma_list = [sigma_op]
    simple_cond_prob = 1.0
    sigma_list_length = len(sigma_list)
    new_sigma_list = remove_unnecessary_parenthesis_in_sigma_list(sigma_list)
    new_sigma_list = apply_rule_4(new_sigma_list)

    while sigma_list_length < len(new_sigma_list):
        '''while rule 4 applied - meaning '''
        sigma_list = new_sigma_list
        new_sigma_list = remove_unnecessary_parenthesis_in_sigma_list(sigma_list)
        new_sigma_list = apply_rule_4(new_sigma_list)
        sigma_list_length = len(sigma_list)
    '''at this point sigma list contains only sigma instances with simple condition '''

    for sigma in new_sigma_list:
        simple_cond_prob *= get_probability_by_condition(sigma.predicate, processed_schema.att_to_v)

    res_schema = Schema("Scheme" + str(processed_schema.name_counter + 1),
                        math.ceil(simple_cond_prob * processed_schema.n_rows), \
                        processed_schema.att_list, processed_schema.att_to_v, \
                        processed_schema.att_to_size, processed_schema.name_counter + 1)

    print("output: " + res_schema.get_estimation_stat_str() + "\n")

    return res_schema


def estimate_njoin(schema_1, schema_2):
    print("NJOIN")
    print("input: " + schema_1.get_estimation_stat_str() + " " + schema_2.get_estimation_stat_str())

    new_att_list = copy.deepcopy(schema_1.att_list)
    new_att_list.extend(copy.deepcopy(schema_2.att_list))
    new_att_to_v = copy.deepcopy(schema_1.att_to_v)
    new_att_to_v.update(copy.deepcopy(schema_2.att_to_v))
    new_att_to_size = copy.deepcopy(schema_1.att_to_size)
    new_att_to_size.update(copy.deepcopy(schema_2.att_to_size))

    njoin_predicate_probability = estimate_njoin_probability(schema_1, schema_2)
    res_schema = Schema("Scheme" + str(schema_1.name_counter + schema_2.name_counter + 1), \
                        math.ceil(schema_1.n_rows * schema_2.n_rows * njoin_predicate_probability), new_att_list, \
                        new_att_to_v, new_att_to_size, schema_1.name_counter + schema_2.name_counter + 1)

    print("output: " + res_schema.get_estimation_stat_str() + "\n")
    return res_schema

def estimate_njoin_probability(schema_1,schema_2):

    res_prob = 1
    col_to_att= {}
    for att in schema_1.att_list:
        col_to_att[att.split(".")[1]] = att

    for att in schema_2.att_list:
        col_name = att.split(".")[1]
        if col_name in col_to_att:
            res_prob *=  max(1/schema_1.att_to_v[col_to_att[col_name]],1/schema_2.att_to_v[att])

    return res_prob


def get_probability_by_condition(curr_sigma_predicate, att_to_v):
    """under the assumption only "=" and simple conditions- design by contract and by given clarifications"""
    copied_predicate = copy.deepcopy(curr_sigma_predicate)
    if copied_predicate[0] == '(' and copied_predicate[-1] == ')' and is_simple_cond(copied_predicate[1:-1]):
        copied_predicate = removeAllOuterParenthesis(copied_predicate)
        copied_predicate = copied_predicate[1:-1]

    parsed_simple_condition = strip_simple_cond_list(copied_predicate.split("="))
    cond_probability = 0.0
    if parsed_simple_condition[0] == parsed_simple_condition[1]:
        cond_probability = 1.0
    elif parsed_simple_condition[0].isnumeric() and not parsed_simple_condition[1].isnumeric():
        att = parsed_simple_condition[1]
        cond_probability = 1.0 / att_to_v[att]
    elif not parsed_simple_condition[0].isnumeric() and parsed_simple_condition[1].isnumeric():
        att = parsed_simple_condition[0]
        cond_probability = 1.0 / att_to_v[att]
    elif not parsed_simple_condition[0].isnumeric() and not parsed_simple_condition[1].isnumeric():
        if is_attribute(parsed_simple_condition[0]) and is_attribute(parsed_simple_condition[1]):
            v_att_0 = att_to_v[parsed_simple_condition[0]]
            v_att_1 = att_to_v[parsed_simple_condition[1]]
            cond_probability = 1.0 / (max(v_att_0, v_att_1))
    else:
        cond_probability = 0.0

    return cond_probability


def is_att_in_list(att, att_list):
    for elem in att_list:
        if att[-1] == elem[-1]:
            return True

    return False


def adjust_expression_list_by_file(expression_list):
    buffer_of_stat_file = open("statistics.txt", "r")
    new_exp_list = copy.deepcopy(expression_list)

    for i in range(2):
        ''' parsing Pair operator - last element in expression list would be of Pair class (design by contract)'''
        info_line = buffer_of_stat_file.readline()[:-1]
        new_exp_list[-1].get_i_elem_in_pair(i)[0].name = info_line.split(" ")[1].strip()
        info_line = buffer_of_stat_file.readline()[:-1]
        """reading without '\n' and  parenthesis"""
        info_line = info_line[2:-1]
        type_list = strip_simple_cond_list(info_line.split(","))
        att_list = []
        att_to_type = {}
        for att in type_list:
            att_list.append(new_exp_list[-1].get_i_elem_in_pair(i)[0].name + "." + att[0])
            att_to_type[new_exp_list[-1].get_i_elem_in_pair(i)[0].name + "." + att[0]] = att.split(":")[1]

        att_to_size = estimate_att_size_list(att_to_type)
        new_exp_list[-1].get_i_elem_in_pair(i)[0].att_list = copy.deepcopy(att_list)
        new_exp_list[-1].get_i_elem_in_pair(i)[0].att_to_size = copy.deepcopy(att_to_size)

        info_line = buffer_of_stat_file.readline()[:-1]
        new_exp_list[-1].get_i_elem_in_pair(i)[0].n_rows = int(info_line.split("=")[1].strip())
        new_exp_list[-1].get_i_elem_in_pair(i)[0].n_width = len(att_list)

        att_to_v = {}
        for att in att_list:
            info_line = buffer_of_stat_file.readline()[:-1]
            att_to_v[att] = int(info_line.split("=")[1].strip())

        new_exp_list[-1].get_i_elem_in_pair(i)[0].att_to_v = copy.deepcopy(att_to_v)
        info_line = buffer_of_stat_file.readline()[:-1]
    buffer_of_stat_file.close()
    return new_exp_list


def estimate_att_size_list(att_to_type):
    att_to_size = {}

    for att in att_to_type:
        if att_to_type[att] == "INTEGER":
            att_to_size[att] = 4

    return att_to_size


def optimize_query(mode, expression_list):
    if mode == "Part 1":
        optimization_rule = get_optimization_rule()
        optimized_exp_list = optimize_expr_by_opt_rule(expression_list.copy(), optimization_rule.strip())
    elif mode == "Part 2":
        '''Making 4 copies of Logical Queries Expressions '''
        for i in range(0, 4):
            list_of_expressions_lists.append(copy.deepcopy(expression_list))
        for i in range(0, 4):
            print("expression before optimization:")
            print_expression_list(list_of_expressions_lists[i])
            print("\n\n", end="")
            for itr in range(0, 10):
                print(f"Iteration {itr + 1} out of 10:")
                list_of_expressions_lists[i] = optimize_expr_by_opt_rule(list_of_expressions_lists[i],
                                                                         num_to_opt_rules_menu[
                                                                             random.choice([1, 2, 3, 4, 5, 6])])

            print(f"just finished optimizing logical query plan {i + 1}\n")

        '''Printing Optimized Expressions'''
        print("\n", end="")
        for i in range(0, 4):
            print(f"optimized expression number {i + 1}:")
            print_expression_list(list_of_expressions_lists[i])
            print("\n", end="")

        return list_of_expressions_lists


def optimize_expr_by_opt_rule(expression_list, optimization_rule):
    optimized_expression_list = []
    if optimization_rule == '4':
        print("Applying optimization rule 4 ...")
        optimized_expression_list = apply_rule_4(expression_list)
        print_expression_list(optimized_expression_list)
        print("\n\n", end="")
    elif optimization_rule == '4a':
        print("Applying optimization rule 4a ...")
        optimized_expression_list = apply_rule_4a(expression_list)
        print_expression_list(optimized_expression_list)
        print("\n\n", end="")
    elif optimization_rule == '5a':
        optimized_expression_list = apply_rule_5a(expression_list)
    elif optimization_rule == '6':
        optimized_expression_list = apply_rule_6(expression_list)
    elif optimization_rule == '6a':
        optimized_expression_list = apply_rule_6a(expression_list)
    elif optimization_rule == '11b':
        optimized_expression_list = apply_rule_11b(expression_list)

    return optimized_expression_list


def apply_rule_4a(expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    lqp_state.append("4a")
    ind_of_pair = None

    for i in range(0, len(expression_list) - 1):
        if isinstance(expression_list[i], Sigma) and isinstance(expression_list[i + 1], Sigma):
            new_exp_list[i + 1].predicate = expression_list[i].predicate
            new_exp_list[i].predicate = expression_list[i + 1].predicate
            break

        if isinstance(expression_list[i + 1], Pair):
            ind_of_pair = i+1

    if ind_of_pair:
        left_list = apply_rule_4a(expression_list[ind_of_pair].left_lst)
        if left_list == expression_list[ind_of_pair].left_lst:
            new_exp_list[ind_of_pair].right_lst = apply_rule_4a(expression_list[ind_of_pair].right_lst)
        else:
            new_exp_list[ind_of_pair].left_lst = left_list

    lqp_state.clear()
    return new_exp_list


def apply_rule_5a(expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    parsed_predicate_att_list.clear()
    lqp_state.append("5a")
    print("Applying optimization rule 5a ...")
    for i in range(0, len(expression_list) - 1):
        if isinstance(expression_list[i], Pi) and isinstance(expression_list[i + 1], Sigma):
            temp_predicate = copy.deepcopy(expression_list[i + 1].predicate)
            parse_predicate_to_att_list(temp_predicate)
            if is_a_contained_in_b(parsed_predicate_att_list, expression_list[i].att_list):
                temp_sigma = new_exp_list.pop(i + 1)
                new_exp_list.insert(i, temp_sigma)
                break;

    print_expression_list(new_exp_list)
    print("\n\n", end="")
    lqp_state.clear()
    return new_exp_list


def parse_predicate_to_att_list(predicate):
    is_condition(predicate)


def is_a_contained_in_b(a_list, b_list):

    for elem in a_list:
        if elem not in b_list:
            return False

    return True


def apply_rule_6(expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    parsed_predicate_att_list.clear()
    lqp_state.append("6")
    print("Applying optimization rule 6 ...")

    for i in range(0, len(expression_list) - 1):
        if isinstance(expression_list[i], Sigma) and (
                isinstance(expression_list[i + 1], Njoin) or isinstance(expression_list[i + 1], Cartesian)):

            '''Under the assumption there are no nested queries and therefore, no nested natural join/cartesian operators '''
            temp_predicate = copy.deepcopy(expression_list[i].predicate)
            parse_predicate_to_att_list(temp_predicate)
            left_att_list = get_scheme_att_list(expression_list[i + 2].left_lst[-1])
            if is_a_contained_in_b(parsed_predicate_att_list, left_att_list):
                new_exp_list[i + 2].left_lst.insert(0, new_exp_list.pop(i))
                break;

    print_expression_list(new_exp_list)
    print("\n\n", end="")
    lqp_state.clear()
    return new_exp_list


def apply_rule_6a(expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    parsed_predicate_att_list.clear()
    lqp_state.append("6a")
    print("Applying optimization rule 6a ...")

    for i in range(0, len(expression_list) - 1):
        if isinstance(expression_list[i], Sigma) and (
                isinstance(expression_list[i + 1], Njoin) or isinstance(expression_list[i + 1], Cartesian)):

            '''Under the assumption there are no nested queries and therefore, no nested natural join/cartesian 
            operators '''
            temp_predicate = copy.deepcopy(expression_list[i].predicate)
            parse_predicate_to_att_list(temp_predicate)
            right_att_list = get_scheme_att_list(expression_list[i + 2].right_lst[-1])
            if is_a_contained_in_b(parsed_predicate_att_list, right_att_list):
                new_exp_list[i + 2].right_lst.insert(0, new_exp_list.pop(i))
                print(f"i'th element {new_exp_list[i]}\n***************")
                break

    print_expression_list(new_exp_list)
    print("\n\n", end="")
    lqp_state.clear()
    return new_exp_list


def get_scheme_att_list(scheme):
    if scheme.name == "R":
        return ['R.A', 'R.B', 'R.C', 'R.D', 'R.E']
    else:
        return ['S.D', 'S.E', 'S.F', 'S.H', 'S.I']


def is_equal_d_col(att_1, att_2):
    return (att_1 == "R.D" and att_2 == "S.D") or (att_1 == "S.D" and att_2 == "R.D")


def is_equal_e_col(att_1, att_2):
    return (att_1 == "S.E" and att_2 == "R.E") or (att_1 == "R.E" and att_2 == "S.E")


def is_njoin_predicate(first_simple_cond_lst, second_simple_cond_lst):
    res_option_1 = (is_equal_e_col(first_simple_cond_lst[0], first_simple_cond_lst[1]) and is_equal_d_col(
        second_simple_cond_lst[0], second_simple_cond_lst[1]))
    res_option_2 = (is_equal_d_col(first_simple_cond_lst[0], first_simple_cond_lst[1]) and is_equal_e_col(
        second_simple_cond_lst[0], second_simple_cond_lst[1]))

    return res_option_1 or res_option_2


def is_11b_need_to_be_applied(cond_to_parse):
    is_applying_needed = False
    cond_to_parse = removeAllOuterParenthesis(cond_to_parse)
    parsed_cond = cond_to_parse.split("AND")
    first_simple_cond_list = []
    second_simple_cond_list = []
    if len(parsed_cond) == 2:
        stripped_first_cond = get_stripped_condition(parsed_cond[0].strip())
        stripped_second_cond = get_stripped_condition(parsed_cond[1].strip())
        if is_simple_cond(stripped_first_cond) and is_simple_cond(stripped_second_cond):
            first_simple_cond_list.extend(stripped_first_cond.split("="))
            second_simple_cond_list.extend(stripped_second_cond.split("="))

        if len(first_simple_cond_list) == 2 and len(second_simple_cond_list) == 2:
            if is_njoin_predicate(strip_simple_cond_list(first_simple_cond_list),
                                  strip_simple_cond_list(second_simple_cond_list)):
                is_applying_needed = True

    return is_applying_needed


def removeAllOuterParenthesis(predicate):
    """using only in case the content of the parenthesis is a valid condition - simplifying multiple parenthesis
    cases """
    content_condition = False
    copied_predicate = copy.deepcopy(predicate)
    if copied_predicate[0] == '(' and copied_predicate[-1] == ')' and is_condition(copied_predicate[1:-1]):
        while len(copied_predicate) > 2 and \
                copied_predicate[0] == '(' and copied_predicate[-1] == ')' \
                and is_condition(copied_predicate[1:-1]):
            copied_predicate = copied_predicate[1:-1]
        copied_predicate = '(' + copied_predicate + ')'

    return copied_predicate


def strip_simple_cond_list(simple_cond_list):
    copy_of_simple_list = copy.deepcopy(simple_cond_list)
    map_result = map(lambda elem : elem.strip(), copy_of_simple_list)

    return  list(map_result)


def get_stripped_condition(cond_str):
    # under the assumption the input is valid (a valid condition)
    stripped_cond = ""
    '''under the assumption the conditions are stripped'''''
    cond_str = removeAllOuterParenthesis(cond_str)
    if is_condition(cond_str[1:-1]):
        stripped_cond += cond_str[1:-1]
    else:
        stripped_cond += cond_str
    # no other case - checking if there are parenthesis or not
    return stripped_cond.strip()


def apply_rule_11b(expression_list):
    new_exp_list = copy.deepcopy(expression_list)
    cond_to_parse = ""
    print("Applying optimization rule 11b ...")
    lqp_state.append("11b")
    for i in range(0, len(expression_list) - 1):
        if isinstance(expression_list[i], Sigma) and isinstance(expression_list[i + 1], Cartesian):
            copied_predicate = copy.deepcopy(expression_list[i].predicate)
            if copied_predicate[0] == "(" and copied_predicate[-1] == ")" \
                    and is_condition(copied_predicate[1:-1]):
                copied_predicate = removeAllOuterParenthesis(copied_predicate)
                cond_to_parse += copied_predicate[1:-1]
            else:
                cond_to_parse += copied_predicate

            if is_11b_need_to_be_applied(cond_to_parse):
                new_njoin = Njoin()
                new_exp_list.insert(i, new_njoin)
                new_exp_list.pop(i + 1)
                new_exp_list.pop(i + 1)
                break

    print_expression_list(new_exp_list)
    print("\n\n", end="")
    lqp_state.clear()
    return new_exp_list


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
    table_lst = table_list_str.split(",")

    expression_list = [pi_elem, sigma_elem, Cartesian(), Pair([Schema(table_lst[0])], [Schema(table_lst[1])])]

    return expression_list


def print_expression_list(expression_list):
    if isinstance(expression_list[0], Pair):
        print_expression_list(expression_list[0].left_lst)
        print(",", end="")
        print_expression_list(expression_list[0].right_lst)
    elif len(expression_list) == 1:
        print(expression_list[0].__str__(), end="")
    else:
        print(expression_list[0].__str__() + "(", end="")
        print_expression_list(expression_list[1:])
        print(")", end="")


def get_partitioned_and_index_aux(cond_str):
    if is_simple_cond(cond_str):
        return -1
    elif cond_str[0] == "(" and cond_str[-1] == ")" and is_condition(cond_str[1:-1]):
        return -1
    elif cond_str.count("AND") > 0:
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
            if attribute_name.strip() == "A" or attribute_name.strip() == "B" or attribute_name.strip() == "C" or \
                    attribute_name.strip() == "D" or attribute_name.strip() == "E":
                if "5a" in lqp_state or "6" in lqp_state or "6a" in lqp_state or "11b" in lqp_state:
                    parsed_predicate_att_list.append(attribute)
                return True

        elif table_name == "S":
            if attribute_name.strip() == "D" or attribute_name.strip() == "E" or attribute_name.strip() == "F" or \
                    attribute_name.strip() == "G" or attribute_name.strip() == "H" or attribute_name.strip() == "I":

                if "5a" in lqp_state or "6" in lqp_state or "6a" in lqp_state or "11b" in lqp_state:
                    parsed_predicate_att_list.append(attribute)
                return True
        else:
            return False


def is_a_string(sql_str):
    return (sql_str[0] == '"' and sql_str[-1] == '"') or (sql_str[0] == "'" and sql_str[-1] == "'") or (
            sql_str[0] == "’" and sql_str[-1] == "’") or (sql_str[0] == "`" and sql_str[-1] == "`")


class Pi:
    def __init__(self, att_list):
        self.att_list = []
        for elem in att_list:
            self.att_list.append(elem.strip())

    def __str__(self):
        representing_str = "PI["
        for col in self.att_list:
            representing_str += (col + ",")
        '''removing the last "," '''
        representing_str = representing_str[0:-1]
        representing_str += "]"

        return representing_str

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.att_list == other.att_list
        else:
            return False


class Sigma:
    def __init__(self, predicate):
        self.predicate = predicate.strip()

    def __str__(self):
        representing_str = "SIGMA["
        representing_str += (self.predicate + "]")

        return representing_str

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.predicate == other.predicate
        else:
            return False


class Cartesian:
    def __init__(self):
        pass

    def __str__(self):
        return "CARTESIAN"


class Njoin:

    def __init__(self):
        pass

    def __str__(self):
        return "NJOIN"


class Schema:

    def __init__(self, name, n_rows=0, att_list=[], att_to_v=[], att_to_size=[], name_counter=0):
        self.name = name.strip()
        self.n_rows = n_rows
        self.n_width = len(att_list)
        self.att_to_v = att_to_v
        self.att_list = strip_simple_cond_list(att_list)
        self.att_to_size = att_to_size
        self.size_of_row = self.calc_row_size()
        self.name_counter = name_counter

    def __copy__(self, other):

        self.name = other.name.strip()
        self.n_rows = other.n_rows
        self.name_counter = other.name_counter
        self.n_width = len(other.att_list)
        self.att_to_v = copy.deepcopy(other.att_to_v)
        self.att_list = copy.deepcopy(other.att_list)
        self.att_to_size = copy.deepcopy(other.att_to_size)
        self.size_of_row = self.calc_row_size()

    def get_estimation_stat_str(self):

        return f"n_{self.name}=" + str(self.n_rows) + f" R_{self.name}=" + str(self.size_of_row)

    def calc_row_size(self):
        row_size = 0
        for att in self.att_to_size:
            row_size += self.att_to_size[att]
        return row_size

    def __str__(self):
        return self.name

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.name == other.name and self.n_rows == other.n_rows and self.n_width == other.n_width
        else:
            return False


class Pair:

    def __init__(self, left_list, right_list):
        self.left_lst = left_list
        self.right_lst = right_list

    def get_i_elem_in_pair(self, i):
        if i == 0:
            return self.left_lst
        elif i == 1:
            return self.right_lst
        else:
            return None

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.left_lst == other.left_lst and self.right_lst == other.right_lst
        else:
            return False


if __name__ == '__main__':
    tester_menu()
