# -*- coding: utf-8 -*-
"""
    Module that tries to optimize valid functions with the polyhedral model using PoCC as an
    optimization tool
"""
from configparser import ConfigParser
from dis import get_instructions
from copy import deepcopy
import os
from subprocess import CalledProcessError
import subprocess

from condition import Condition
from loop import Loop
from polynom import Polynom
from scoplib import ScopLib
from statement import Statement
from tree import Tree
from variable import Variable


def __code_from_condition(condition, iterator, is_start):
    """
        Returns the code corresponding to a given condition of a loop statement

    Parameters
    ----------
        condition : the condition_text to convert to code
        iterator : the iterator of the loop this condition_text resides on
        is_start : True if this condition_text is from the start part of the loop and False if it is
            from the end part

    Returns
    -------
        String containing the code of the condition_text
    """
    code = ''
    aux = []
    divisor = 1
    for p in condition.coefficients.keys():
        if p == iterator:
            if (condition.coefficients[p] == 1 and is_start) or (condition.coefficients[p] == -1 and not is_start):
                pass
            else:
                divisor = abs(condition.coefficients[p])
        elif condition.coefficients[p] != 1:
            aux.append(str(p) + ' * ' + str(condition.coefficients[p]))
        else:
            aux.append(str(p))
    code += ' + '.join(aux)
    if condition.term is not None and condition.term != 0:
        if condition.term > 0 and code != '':
            code += ' + ' + str(condition.term)
        else:
            code += str(condition.term)
    if divisor != 1:
        code = '(' + code + ')//' + str(divisor)
    return code


def __get_loop_code(iterator, start_conditions, end_conditions, indentation):
    """
        Returns the code corresponding to a loop

    Parameters
    ----------
    iterator : name of the iterator variables
    start_conditions : list of conditions from the start part of the loop
    end_conditions  : list of conditions from the end part of the loop
    indentation : number of identations this loop has

    Returns
    -------
        A string corresponding to the loop statement described by the inputs

    Raises
    ------
        ValueError: if the iterator is not provided
    """

    code = 'for {} in range ({}{}):\n'
    if iterator is None:
        raise ValueError('Missing iterator')
    if not end_conditions:
        return '\n'

    # Start
    if not start_conditions:
        loop_start = ''
    elif len(start_conditions) == 1:
        loop_start = __code_from_condition(start_conditions[0], iterator, True)
    else:
        aux = []
        for x in start_conditions:
            condition = __code_from_condition(x, iterator, True)
            if condition != '':
                aux.append(condition)
            else:
                aux.append('0')
        if len(aux) > 1:
            loop_start = 'max({})'.format(' , '.join(aux))
        else:
            loop_start = aux[0]

    # Separator between start and end
    if not (loop_start == '' or loop_start.isspace()):
        loop_start += ' , '

    # End
    if len(end_conditions) == 1:
        condition = __code_from_condition(end_conditions[0], iterator, False)
        if (condition != ''):
            condition = '(' + condition + ')+1'
        loop_end = condition
    else:
        aux = []
        for condition in end_conditions:
            condition = __code_from_condition(condition, iterator, False)
            if condition != '':
                aux.append('(' + condition + ')+1')
            else:
                aux.append('0')
        if len(aux) > 1:
            loop_end = 'min({})'.format(' , '.join(aux))
        else:
            loop_end = aux[0]

    return indentation * '    ' + code.format(iterator, loop_start, loop_end)


def __get_if_statement_condition(conditions, indentation):
    """
        Returns the code corresponding to a if condition_text with the conditions provided
    Parameters
    ----------
        conditions : list of conditions that make the if statement
        indentation : indentation of the condition_text

    Returns
    -------
        The code corresponding to an if condition_text
    """
    code = indentation * '    ' + 'if({}):\n'
    processed_conditions = []
    for condition in conditions:
        processed_conditions.append('(' + condition.string_form() + ('>= 0)' if condition.greater_than else ' == 0)'))
    result = ' and '.join(processed_conditions)
    return code.format(result)


def __get_statement_code(statement, conditions, indentation):
    """
        Generates the code corresponding to a given statement

    Parameters
    ----------
        statement : statement object to convert to code
        conditions  : list of conditions that affect the statement. If there are any, the statement
            is enclosed inside an if statement.
        indentation : number of indentations of this statement

    Returns
    -------
        A string containing the code corresponding to this statement
    """
    code = ''
    if conditions:
        code += __get_if_statement_condition(conditions, indentation)
        indentation += 1

    code += indentation * '    ' + statement.code[:-1] + '\n'  # -1 to get rid of the ; that PoCC inserts
    return code


def __calculate_all_conditions(tree, possible_coefficients):
    """
        For each node of the tree, it floats all the conditions that are common to ALL the
        children to the parent, removing them from the children
    Parameters
    ----------
        tree : the tree to calculate the conditions
        possible_coefficients : list of all the parameters and the names of all the fathers

    Returns
    -------
        The tree with the conditions recalculated
    """
    if tree.branches:
        for branch in tree.branches:
            __calculate_all_conditions(branch, possible_coefficients + [tree.name])

        conditions = []
        for branch in tree.branches:
            for condition in branch.conditions:
                for branch_2 in tree.branches:
                    if condition not in branch_2.conditions:
                        break
                else:
                    for condition_2 in conditions:
                        if condition == condition_2:
                            break
                    else:
                        for key in condition.coefficients.keys():
                            if key not in possible_coefficients + [tree.name]:
                                break
                        else:
                            conditions.append(condition)
        tree.conditions = conditions
        for branch in tree.branches:
            for condition in tree.conditions:
                branch.conditions.remove(condition)
    else:
        for loop in tree.data.loops:
            tree.conditions += loop.loop_conditions
        for condition in tree.data.if_conditions:
            tree.conditions.append(condition)

    return tree


def __tree_from_statements(statements, parameters):
    """
        Creates a tree from the statements, where the leaves are the statements and the nodes are
        the loops, except the top node that is the base level (no scope)
    Parameters
    ----------
        statements : lsit of statements that will form the leaves
        parameters : list of all the parameters of the scop

    Returns
    -------
        The tree object made from all the statements
    """
    tree = Tree()
    tree.name = 'AuxiliarScope'

    for st, statement in enumerate(statements):
        t = tree
        for sc, scat in enumerate(statement.scattering):
            if scat is statement.scattering[-1]:
                leaf = Tree()
                leaf.data = statement
                leaf.name = 'statement ' + str(st + 1)
                t.branches.insert(int(scat[1]), leaf)

            if len(t.branches) <= int(scat[1]):  # The branch doesn't exist
                new = Tree()
                new.name = statement.scattering[sc + 1][0]
                t.branches.insert(int(scat[1]), new)
            t = t.branches[int(scat[1])]

    __calculate_all_conditions(tree, parameters)
    return tree


def __get_code(tree, code='', indentation=0):
    """
        Returns a string that contains the code described by a given tree.
    Parameters
    ----------
        tree : a tree object that describes a code
        code : used in recursion (default = '')
        indentation : indentation of the code (default = '')

    Returns
    -------
        A string of containing the code described by the tree
    """
    if tree.branches:  # not a statement
        if tree.conditions:
            start_conditions = []
            end_conditions = []
            if_conditions = []
            iterator = tree.name
            if tree.name == 'AuxiliarScope':
                code += __get_if_statement_condition(tree.conditions, indentation + 1)
                indentation += 1
                for branch in tree.branches:
                    code = __get_code(branch, code, indentation + 1)
            else:
                for condition in tree.conditions:
                    if tree.name in condition.coefficients.keys():  # The condition_text is from the loop, not an if
                        if condition.coefficients[tree.name] >= 0:
                            for key in condition.coefficients.keys():  # Start conditions's coefficients are inverted
                                if key != iterator:
                                    condition.coefficients[key] *= -1
                            condition.term *= -1
                            start_conditions.append(condition)
                        else:
                            #condition.term += 1  # Range is <, while the condition_text is <=
                            end_conditions.append(condition)
                    else:
                        if_conditions.append(condition)
                if if_conditions:
                    code += __get_if_statement_condition(if_conditions, indentation)
                    indentation += 1
                code += __get_loop_code(iterator, start_conditions, end_conditions, indentation)
                for branch in tree.branches:
                    code = __get_code(branch, code, indentation + 1)
        else:
            for branch in tree.branches:
                code = __get_code(branch, code, indentation + 1)
    else:
        code += __get_statement_code(tree.data, tree.conditions, indentation)

    return code


def __calculate_range_of_iterations(code_block, parameters, var_id_by_var_name, number, iterator):
    """
        Creates a loop object based on the block of bytecode instructions given. Any new parameter
        will be added to the parameter list. If any new variables appear, the number will be
        incremented and added to the dictionary of variables
    Parameters
    ----------
        code_block : list of bytecode instructions corresponding to a for instruction. From the
            SETUP_LOOP to the line before FOR_LOOP
        parameters : the list of parameters of the scop
        var_id_by_var_name : dictionary associating variable_string names with their corresponding
            number
        number : the max number already associated to a variable_string inside a list so it
            becomes mutable
        iterator : name of the iterator

    Returns
    -------
        A new instance of Loop with the information extracted from the block

    Raises
    ------
        ValueError if the step is different to 1, because SCoPLib doesn't accept different
            values to 1
    """
    start_conditions = []
    end_conditions = []
    step = 1

    stack = []
    for line in code_block:
        if line.opname == 'SETUP_LOOP':
            pass
        elif line.opname == 'GET_ITER':
            pass
        elif line.opname == 'LOAD_GLOBAL':
            stack.append(line.argval)
        elif line.opname == 'LOAD_CONST':
            stack.append(str(line.argval))
        elif line.opname == 'LOAD_FAST':
            stack.append(line.argval)
            if '|' + str(line.argval) + '|' not in var_id_by_var_name:
                parameters.append(str(line.argval))
                number[0] += 1
                var_id_by_var_name['|' + str(line.argval) + '|'] = number[0]
        elif line.opname == 'BINARY_SUBSCR':
            tos = stack.pop()
            tos1 = stack.pop()
            stack.append(tos1[tos])
        elif line.opname == 'BINARY_ADD':
            tos = stack.pop()
            tos1 = stack.pop()
            stack.append(tos + '|+|' + tos1)
        elif line.opname == 'BINARY_SUBTRACT':
            tos = stack.pop()
            tos1 = stack.pop()
            stack.append(tos + '|-|' + tos1)
        elif line.opname == 'BINARY_MULTIPLY':
            tos = stack.pop()
            tos1 = stack.pop()
            stack.append(tos + '|*|' + tos1)
        elif line.opname == 'CALL_FUNCTION':
            args = []
            for _ in range(int(line.argval)):
                args.append(stack.pop())
            tos = stack.pop()
            stack.append(str(tos) + '(' + str(args) + ')')
            if str(tos) == 'range':
                if len(args) >= 1:
                    if 'min' not in args[0] and 'max' not in args[0]:
                        polynom = __analyze_polynom(args[0], [], parameters, [-1], var_id_by_var_name)
                        condition = Condition()
                        condition.term = polynom.term
                        condition.coefficients = polynom.coefficients
                        condition.coefficients['|' + iterator + '|'] = -1
                        end_conditions.append(condition)
                if len(args) >= 2:
                    if 'max' not in args[1] and 'min' not in args[1]:
                        polynom = __analyze_polynom(args[1], [], parameters, [-1], var_id_by_var_name)
                        condition = Condition()
                        condition.term = polynom.term
                        condition.coefficients = polynom.coefficients
                        condition.coefficients['|' + iterator + '|'] = 1
                        start_conditions.append(condition)
                else:
                    condition = Condition()
                    condition.coefficients['|' + iterator + '|'] = 1
                    start_conditions.append(condition)  # If not conditions on the start, a 0 will be added by default
                if len(args) >= 3:
                    step = args[2]
                else:
                    step = 1

            elif str(tos) == 'len':
                raise ValueError('len operation inside range arguments')
            elif str(tos) == 'max':
                for arg in args:
                    polynom = __analyze_polynom(arg, [], parameters, [-1], var_id_by_var_name)
                    condition = Condition()
                    condition.term = polynom.term
                    condition.coefficients = polynom.coefficients
                    start_conditions.append(condition)
            elif str(tos) == 'min':
                for arg in args:
                    polynom = __analyze_polynom(arg, [], parameters, [-1], var_id_by_var_name)
                    condition = Condition()
                    condition.term = polynom.term
                    condition.coefficients = polynom.coefficients
                    end_conditions.append(condition)
        else:
            print("DEBUG: argument not considered", line.opname)
            for x in code_block:
                print("DEBUG: code block: ", x)
            raise ValueError('DEBUG: value not considered')

    # All coefficients from the start will be inverted except for the corresponding to the iterator.
    for condition in start_conditions:
        for coefficient in condition.coefficients.keys():
            if coefficient != '|' + iterator + '|':
                condition.coefficients[coefficient] *= -1
        condition.term *= -1

    # The terms of the end condition_text will be subtracted 1 because range uses < while SCoPLib uses <=
    for condition in end_conditions:
        condition.coefficients['|' + iterator + '|'] = -1
        condition.term -= 1

    loop = Loop()
    loop.loop_conditions += start_conditions
    loop.loop_conditions += end_conditions
    if step != 1:
        raise ValueError('Step must be 1')
    return loop


def __analyze_polynom(polynom_string, loops, parameters, number, var_id_by_var_name):
    """
        Given a string of a polynom, it returns the polynom object that represents the same string.
            If a new parameter is found in the polynom_string it will be added to the parameter
            list. Any new variables found will be added to the dictionary and number will be
            incremented accodingly

    Parameters
    ----------
        polynom_string : string of a polynom where all the values are tokenized. i.e. inside | |
        loops : list of all the loops under which this polynom resides.
        parameters : list of parameters
        number : the max number already associated to a variable_string inside a list so it
            becomes mutable
        var_id_by_var_name : dictionary associating variable_string names with their corresponding
            number

    Returns
    -------
        A polynom object that represents the input polynom
    """
    pol = Polynom()
    sums = polynom_string.split('|+|')
    coefficients = {}
    for product in sums:
        product = product.replace('(', '').replace(')', '')
        try:  # term case
            term = eval(product.replace('|', ''))
            pol.term += term
            continue
        except (NameError, SyntaxError):
            # An error indicates that the product is different of a single number, so we know its a product
            pass
        elements = product.split('|*|')
        name = None
        # On a list for the case of the value appearing before the variable_string, the value will be maintained
        coefficient = [1]
        for element in elements:
            element = element.replace('|', '')
            try:
                c = int(element)
                coefficient[0] *= c
                continue
            except ValueError:
                for loop in loops:
                    if loop.iterator.replace('|', '') == element:
                        name = loop.iterator
                        break
                if name is not None:
                    coefficients['|' + name + '|'] = coefficient
                else:
                    if element not in parameters:
                        if '|' + str(element) + '|' not in var_id_by_var_name.keys():
                            # Iterator variables are assigned a number and added to the dictionary
                            number[0] += 1
                            var_id_by_var_name['|' + str(element) + '|'] = number[0]
                        parameters.append(element)
                    coefficients['|' + str(element) + '|'] = coefficient

                continue

    for x in coefficients.keys():  # Coefficients are taken out of the list since now its not necessary
        pol.coefficients[x] = coefficients[x][0]

    return pol


def __analyze_var(variable_string, var_id_by_var_name, loops, number, parameters):
    """
        Given a string of a variable, it returns the variable object that represents the same
            string. If a new parameter is found in the variable_string it will be added to the
            parameter list. Any new variables found will be added to the dictionary and number
            will be incremented accordingly

    Parameters
    ----------
        variable_string : string of a variable where all the values are tokenized. i.e. inside | |
        var_id_by_var_name : dictionary associating variable_string names with their corresponding
            number
        loops : list of all the loops under which this polynom resides
        number : the max number already associated to a variable_string inside a list so it becomes
            mutable
        parameters : list of parameters
    Returns
    -------
        A variable object that represents the input polynom
    """
    result_variables = []

    if '|,|' in variable_string:  # When the variable is an argument of a function, it must be split
        variables = variable_string.split('|,|')
    else:
        variables = [variable_string]

    for variable_string in variables:
        try:  # If the variable is a number
            float(variable_string.replace('|', '').replace(')', '').replace('(', ''))
            return []
        except ValueError:
            pass

        variable_string = variable_string.replace(']', '').replace('(', '').replace(')', '')
        ls = variable_string.split('[')
        var_name = ls[0]
        indexes = []
        if len(ls) > 1:
            for e in ls[1:]:
                indexes.append(__analyze_polynom(e, loops, parameters, number, var_id_by_var_name))

        is_var_id_known = next((x for x in var_id_by_var_name.keys() if x == var_name), False)
        if not is_var_id_known:
            number[0] += 1
            result_variable = Variable(var_name, number[0])
            var_id_by_var_name[var_name] = number[0]
        else:
            result_variable = Variable(var_name, var_id_by_var_name[var_name])

        result_variable.index = indexes

        if indexes:  # Case when the variable is a list of a matrix
            result_variable.index_text = '[' + ']['.join(ls[1:]) + ']'
        else:  # Case that the variable doesn't have an index
            result_variable.index_text = '[0]'
        result_variables.append(result_variable)

    return result_variables


def __separate_vars(var_string):
    """
        Separates a variable with the form a[x]+b[y] in [a[x], b[y]], returning them as a list

    Parameters
    ----------
     var_string : string of a sum of variables

    Returns
    -------
        A list of the variables separated
    """
    analyzed_string = ''
    in_variable = False
    for i, char in enumerate(var_string):
        if char == '[':
            in_variable = True
        elif char == ']':
            in_variable = False
        elif char in ('+', '/', '*', '-') and not in_variable and var_string[i + 1] == '|':
            # Followed by a '|' to avoid the - in negative number
            char = '#'
        analyzed_string += char
    # This makes the ',' added in CALL_FUNCTIONS treated. The ',' is necessary to build the body
    analyzed_string.replace(',', '#')

    return analyzed_string.split('|#|')


def __analyze_condition(condition_text, loops, parameters, number, var_Id_by_varName):
    """
        Generates a condition object based on a tokenized string representing a condition
            Parameters
    ----------
        condition_text : string of a condition where all the values are tokenized. i.e. inside | |
        loops : list of all the loops under which this polynom resides
        parameters : list of parameters
        number : the max number already associated to a variable_string inside a list so it becomes
                mutable
        var_Id_by_varName : dictionary associating variable_string names with their corresponding
                number

    Returns
    -------
        A condition object that represents the input condition

    """
    condition_text = condition_text[1:-1]  # Parenthesis are deleted
    if '<' in condition_text:
        if '=' in condition_text:
            left, right = condition_text.split('|<=|')
        else:
            left, right = condition_text.split('|<|')
        is_greater_than = True
        processed = str(left) + '|+||-1||*|' + str(right)
    elif '>' in condition_text:
        if '=' in condition_text:
            left, right = condition_text.split('|>=|')
        else:
            left, right = condition_text.split('|>|')
        is_greater_than = True
        processed = str(right) + '|+||-1||*|' + str(left)
    else:
        left, right = condition_text.split('|==|')
        is_greater_than = False
        processed = str(left) + '|+||-1||*|' + str(right)

    analyzed = __analyze_polynom(processed, loops, parameters, number, var_Id_by_varName)
    condition = Condition()
    condition.coefficients = analyzed.coefficients
    condition.term = analyzed.term
    condition.greater_than = is_greater_than
    return condition


def __obtain_statements_info(code_block, loops, if_conditions, var_id_by_var_name, number, parameters, scattering):
    """
        Obtains the list of statement objects that appear in the code_block
    Parameters
    ----------
        code_block: list of bytecode instructions of the block of code to analyze
        loops: list of loops under which this scope resides
        if_conditions: list of conditions under which this scop resides
        var_id_by_var_name: dictionary that maps a variable name to its corresponding number
        number: last number asigned to a variable inside a list. It needs to be inside a list so its passed by value
        parameters: list of the names of the parameters for this scope
        scattering: list of tuples of the scattering of the previous statements

    Returns
    -------
        A list of all the statements of the code_block as Statement objects
    """
    loop_start = 0
    # First loop start (there's always at least one)
    for i, line in enumerate(code_block):
        if line.opname == 'FOR_ITER':
            iterator = code_block[i + 1].argval
            loop_info = __calculate_range_of_iterations(code_block[:i - 1], parameters,
                                                        var_id_by_var_name, number, iterator)
            loop_info.iterator = iterator
            loop_info.if_conditions = if_conditions
            if_conditions = []
            if '|' + str(loop_info.iterator) + '|' not in var_id_by_var_name.keys():
                number[0] += 1
                var_id_by_var_name['|' + str(loop_info.iterator) + '|'] = number[0]
            loops = loops + [loop_info]
            if scattering:  # Before adding a new scattering the previous is incremented
                scattering[-1][1] += 1
            scattering.append([loop_info.iterator, -1])
            loop_start = i + 2
            break

    # Se itera todos los statement hasta acabar
    in_loop = False
    loop_stack = 0
    start = 0
    statements = []
    stack = []
    body = []
    current_statement = Statement()
    for i, line in enumerate(code_block[loop_start:]):
        # caso de bucles anidados
        if line.opname == 'SETUP_LOOP':
            if loop_stack == 0:
                start = i
            loop_stack += 1
            in_loop = True
        elif line.opname == 'POP_BLOCK':
            loop_stack -= 1
            if loop_stack == 0:
                statements.extend(
                    __obtain_statements_info(code_block[loop_start + start + 1:i + loop_start], loops, if_conditions,
                                             var_id_by_var_name, number, parameters, scattering))
                in_loop = False
        # Caso no es un bucle, por lo que busca statements
        else:
            if not in_loop:
                if line.opname == 'STORE_FAST':
                    tos = str(stack.pop())
                    b = str(body.pop())
                    wrote_var = '|' + str(line.argval) + '|'
                    current_statement.code = str(line.argval) + '=' + b
                    current_statement.wrote_vars += __analyze_var(wrote_var, var_id_by_var_name, loops, number,
                                                                  parameters)
                    for var in __separate_vars(tos):
                        current_statement.read_vars += __analyze_var(var, var_id_by_var_name, loops, number, parameters)
                    current_statement.loops = loops.copy()
                    scattering[-1][1] += 1  # Se aumenta en una posicion el scattering actual
                    current_statement.scattering = deepcopy(scattering)
                    current_statement.if_conditions = if_conditions
                    if_conditions = []
                    for loop in current_statement.loops:
                        current_statement.original_iterator_names.append(loop.iterator)

                    statements.append(current_statement)
                    current_statement = Statement()
                elif line.opname == 'STORE_SUBSCR':
                    tos = str(stack.pop())  # Index
                    tos1 = str(stack.pop())  # Varname
                    tos2 = str(stack.pop())
                    stack.append(tos1 + '[' + tos + ']|=|' + tos2)
                    b = str(body.pop())  # Index
                    b1 = str(body.pop())  # Varname
                    b2 = str(body.pop())
                    body.append(b1 + '[' + b + ']=' + b2)
                    current_statement.code = body.pop()
                    current_statement.wrote_vars += __analyze_var(stack[-1].split('|=|')[0], var_id_by_var_name, loops,
                                                                  number, parameters)
                    for var in __separate_vars(stack[-1].split('|=|')[1]):
                        current_statement.read_vars += __analyze_var(var, var_id_by_var_name, loops, number, parameters)
                    current_statement.loops = loops.copy()
                    scattering[-1][1] += 1  # Se aumenta en una posicion el scattering actual
                    current_statement.scattering = deepcopy(scattering)
                    current_statement.if_conditions = if_conditions
                    if_conditions = []
                    for loop in current_statement.loops:
                        current_statement.original_iterator_names.append(loop.iterator)
                    statements.append(current_statement)
                    current_statement = Statement()
                elif line.opname == 'LOAD_FAST':
                    stack.append('|' + format(line.argval) + '|')
                    body.append(format(line.argval))
                elif line.opname == 'LOAD_CONST':
                    stack.append('|' + format(line.argval) + '|')
                    body.append(format(line.argval))
                elif line.opname == 'LOAD_GLOBAL':
                    stack.append(line.argval)
                    body.append(line.argval)
                elif line.opname == 'DUP_TOP':
                    tos = stack.pop()
                    stack.append(tos)
                    stack.append(tos)
                    b = body.pop()
                    body.append(b)
                    body.append(b)
                elif line.opname == 'DUP_TOP_TWO':
                    tos = stack.pop()
                    tos1 = stack.pop()
                    stack.append(tos1)
                    stack.append(tos)
                    stack.append(tos1)
                    stack.append(tos)
                    b = body.pop()
                    b1 = body.pop()
                    body.append(b1)
                    body.append(b)
                    body.append(b1)
                    body.append(b)
                elif line.opname == 'ROT_TWO':
                    tos = stack.pop()
                    tos1 = stack.pop()
                    stack.append(tos)
                    stack.append(tos1)
                    b = body.pop()
                    b1 = body.pop()
                    body.append(b)
                    body.append(b1)
                elif line.opname == 'ROT_THREE':
                    tos = stack.pop()
                    tos1 = stack.pop()
                    tos2 = stack.pop()
                    stack.append(tos)
                    stack.append(tos2)
                    stack.append(tos1)
                    b = body.pop()
                    b1 = body.pop()
                    b2 = body.pop()
                    body.append(b)
                    body.append(b2)
                    body.append(b1)
                elif line.opname == 'BINARY_ADD' or line.opname == 'INPLACE_ADD':
                    tos = str(stack.pop())
                    tos1 = str(stack.pop())
                    stack.append('(' + tos1 + '|+|' + tos + ')')
                    b = body.pop()
                    b1 = body.pop()
                    body.append('(' + b1 + '+' + b + ')')
                elif line.opname == 'BINARY_SUBTRACT' or line.opname == 'INPLACE_SUBTRACT':
                    tos = str(stack.pop())
                    tos1 = str(stack.pop())
                    stack.append('(' + tos1 + '|+|(|-1||*|' + tos + '))')
                    b = str(body.pop())
                    b1 = str(body.pop())
                    body.append('(' + b1 + '+(-1*' + b + '))')
                elif line.opname == 'BINARY_MULTIPLY' or line.opname == 'INPLACE_MULTIPLY':
                    tos = str(stack.pop())
                    tos1 = str(stack.pop())
                    stack.append('(' + tos1 + '|*|' + tos + ')')
                    b = str(body.pop())
                    b1 = str(body.pop())
                    body.append('(' + b1 + '*' + b + ')')
                elif line.opname == 'BINARY_TRUE_DIVIDE' or line.opname == 'INPLACE_TRUE_DIVIDE':
                    tos = str(stack.pop())
                    tos1 = str(stack.pop())
                    stack.append('(' + tos1 + '|/|' + tos + ')')
                    b = str(body.pop())
                    b1 = str(body.pop())
                    body.append('(' + b1 + '/' + b + ')')
                elif line.opname == 'BINARY_SUBSCR':
                    tos = str(stack.pop())  # Index
                    tos1 = str(stack.pop())  # varName
                    stack.append('(' + tos1 + '[' + tos + '])')
                    b = body.pop()
                    b1 = body.pop()
                    body.append('(' + b1 + '[' + b + '])')
                elif line.opname == 'COMPARE_OP':
                    tos = stack.pop()
                    tos1 = stack.pop()
                    stack.append('(' + tos + '|' + str(line.argval) + '|' + tos1 + ')')
                    b = str(body.pop())
                    b1 = str(body.pop())
                    body.append('(' + b + str(line.argval) + b1 + ')')
                elif line.opname == 'UNARY_NEGATIVE':
                    tos = stack.pop()
                    stack.append('(-1*' + tos + ')')
                    b = str(body.pop())
                    body.append('(-1*' + b + ')')
                elif line.opname == 'JUMP_ABSOLUTE':
                    pass
                elif line.opname == 'POP_BLOCK':
                    pass
                elif line.opname == 'POP_JUMP_IF_TRUE':
                    tos = stack.pop()
                    body.pop()
                    condition = __analyze_condition(tos, loops, parameters, number, var_id_by_var_name)
                    if_conditions.append(condition)
                elif line.opname == 'POP_JUMP_IF_FALSE':
                    tos = stack.pop()
                    body.pop()
                    condition = __analyze_condition(tos, loops, parameters, number, var_id_by_var_name)
                    if_conditions.append(condition)
                elif line.opname == 'CALL_FUNCTION':
                    args = []
                    b = []
                    for _ in range(line.argval):
                        args.append(stack.pop())
                        b.append(body.pop())
                    stack.pop()  # funcion a ejecutar
                    args.reverse()
                    b.reverse()
                    stack.append('|,|'.join(args))
                    body.append(str(body.pop()) + '(' + ', '.join(b) + ')')
                elif line.opname == 'EXTENDED_ARG':
                    pass
                else:
                    print("DEBUG: argument not considered", line.opname)
                    for x in code_block:
                        print("DEBUG: code block: ", x)
                    raise ValueError('DEBUG: value not considered')

    scattering.pop()
    for loop in loops:  # Iterator variables are deleted from the parameters
        if loop.iterator in parameters:
            parameters.remove(loop.iterator)
    return statements


def __optimize_loops(function, debug_mode):
    """
        Tries to optimize a function.
    Parameters
    ----------
        function : the function whose loops have to be optimized
        debug_mode : if True the files used in the optimization are not deleted

    Returns
    -------
        An optimized version of the function or the original code if the
        optimization failed

    Raises
    ------
        CalledProcessError : if the optimization fails
    """
    config = ConfigParser()
    config.read('polypy.conf')
    pocc_path = config['DEFAULT']['pocc_path']

    generate_scoplib_file(function, 'polypy')

    # Optimization of SCoPLib

    optimization_process = subprocess.Popen([pocc_path + ' --read-scop polypy.scop --pluto-tile'],
                                            shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    optimization_process.wait()
    optimization_process_output, optimization_process_output_error = optimization_process.communicate()
    if str(optimization_process_output) == 'b\'\'':
        if debug_mode:
            for line in optimization_process_output_error.decode('utf-8').split('\n'):
                print('DEBUG:', line, '\n')
        raise CalledProcessError(1, 'pocc --read-scop polypy.scop --pluto-tile from')
    else:
        if debug_mode:
            print('DEBUG: output_scop_output')
            for line in optimization_process_output.decode('utf-8').split('\n'):
                print('DEBUG:', line)
            print('\n\n\n')

    output_scop_process = subprocess.Popen([pocc_path + ' --output-scop polypy.pocc.c '],
                                           shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output_scop_process.wait()
    output_scop_output, output_scop_error = output_scop_process.communicate()
    if str(output_scop_output) == 'b\'\'':
        if debug_mode:
            for line in output_scop_error.decode('utf-8').split('\n'):
                print('DEBUG:', line, '\n')
        raise CalledProcessError(1, 'pocc --output-scop')
    else:
        if debug_mode:
            print('DEBUG: output_scop_output')
            for line in output_scop_output.decode('utf-8').split('\n'):
                print('DEBUG:', line)
            print('\n\n\n')

    # Obtainment of code
    code = get_code_from_scoplib('polypy.pocc.pocc.c.scop')

    # Cleanup
    if not debug_mode:
        if os.path.exists('polypy.scop'):
            os.remove('polypy.scop')
        if os.path.exists('polypy.pocc.c'):
            os.remove('polypy.pocc.c')
        if os.path.exists('polypy.pocc.c.scop'):
            os.remove('polypy.pocc.c.scop')
        if os.path.exists('polypy.pocc.pocc.c'):
            os.remove('polypy.pocc.pocc.c')
        if os.path.exists('polypy.pocc.pocc.c.scop'):
            os.remove('polypy.pocc.pocc.c.scop')

    return code


def __decompile_header(function):
    """
        Creates the code definition of a function based on a function bytecode

    Parameters
    ----------
    function : the function to get the header

    Returns
    -------
        A code string of the definition of the function provided
    """
    code = 'def '
    code += str(function.__code__.co_name)
    code += '('
    code += ','.join(function.__code__.co_varnames[:function.__code__.co_argcount])
    code += '):\n'
    return code


def __decompile_return(return_bytecode):
    """
        Creates the return statement based on the bytecode of the return aprt
    Parameters
    ----------
        return_bytecode : list of instructions that make the return statement

    Returns
    -------
        The string of code corresponding to the return statement
    """
    code = ''
    stack = []
    for line in return_bytecode:
        if line.opname == 'LOAD_FAST':
            stack.append(line.argval)
        if line.opname == 'LOAD_CONST':
            stack.append(line.argval)
        elif line.opname == 'LOAD_NAME':
            stack.append(line.argval)
        elif line.opname == 'LOAD_GLOBAL':
            stack.append(line.argval)
        elif line.opname == 'BUILD_TUPLE':
            args = []
            for _ in range(line.argval):
                args.append(str(stack.pop()))
            args.reverse()
            stack.append('(' + ','.join(args) + ')')
        elif line.opname == 'RETURN_VALUE':
            return_value = stack.pop()
            if return_value is not None:
                code = '    return ' + str(return_value)
            else:
                return ''

    return code


def __generate_scoplib_from_loop(code_block):
    """
        Generates a scoplib file from a given bytecode
    Parameters
    ----------
    code_block: list of bytecode instructions from a loop

    Returns
    -------
        A scoplib file
    """
    # Creation of SCoPLib object
    var_id_by_var_name = {}
    statements = []
    parameters = []
    number = [0]

    stack = 0
    start = 0
    base_level_scattering = -1
    for i, _ in enumerate(code_block):
        if code_block[i].opname == 'SETUP_LOOP':
            stack += 1
            if stack == 1:
                start = i
        elif code_block[i].opname == 'POP_BLOCK':
            stack -= 1
            if not stack:
                statements.extend(
                    __obtain_statements_info(code_block[start:i + 1], [], [], var_id_by_var_name, number, parameters,
                                             [['BaseLevelScattering', base_level_scattering]]))
                base_level_scattering += 1

    scoplib = ScopLib()
    # Necesario que sea C para PoCC
    scoplib.language = 'C'
    scoplib.context = [0, 2 + len(parameters)]
    scoplib.parameters = parameters
    scoplib.statements = statements

    return scoplib


def __separate_return_block(code):
    """
        Separates the body of a function from the return statement
    Parameters
    ----------
        code: list of bytecode instructions of a function

    Returns
    -------
        A tuple in which its first value is the code corresponding to the body of a function and the second to
        the return value
    """
    first_setup_loop = None
    last_pop_block = None
    for i, line in enumerate(code):
        if line.opname == 'SETUP_LOOP' and first_setup_loop is None:
            first_setup_loop = i
        elif line.opname == 'POP_BLOCK':
            last_pop_block = i

    return code[first_setup_loop:last_pop_block + 1], code[last_pop_block + 1:]


def generate_scoplib_file(function, filename=''):
    """
        Generates a .scop file from the given function
    Parameters
    ----------
        function: list of bytecode instructions of a loop
        filename: name of the resulting file (default = the same as the function)

    Returns
    -------
        None
    """
    if filename == '':
        filename = function.__code__.co_name
    filename += '.scop'

    code = list(get_instructions(function))
    function_body, _ = __separate_return_block(code)

    scoplib = __generate_scoplib_from_loop(function_body)

    with open(filename, 'w') as scoplib_file:
        scoplib_file.write(scoplib.file_representation())


def get_code_from_scoplib(scoplib_file):
    """
        Generates a string of code representing the information on a scoplib file
    Parameters
    ----------
        scoplib_file: a scoplib file

    Returns
    -------
        A string of code representing the scoplib object

    """
    scoplib = ScopLib(scoplib_file)
    tree = __tree_from_statements(scoplib.statements, scoplib.parameters)
    code = __get_code(tree)
    return code


def optimize(function, debug_mode=False):
    """
        Returns a function optimized with the polyhedral model. If the function cannot be
            optimized the original function is returned

    Parameters
    ----------
        function : the function to be optimized
        debug_mode : if True, the optimized function will be printed in the console and the
            optimization files will
        not be deleted. (default = False)

    Returns
    -------
        The function optimized
    """
    code = list(get_instructions(function))
    optimized_code = ''

    _, function_return = __separate_return_block(code)

    optimized_code += __decompile_header(function)
    try:
        optimized_code += __optimize_loops(function, debug_mode)
    except CalledProcessError:
        generate_scoplib_file(function, 'aux')
        optimized_code += get_code_from_scoplib('aux.scop')
        if os.path.exists('aux.scop'):
            os.remove('aux.scop')

    optimized_code += __decompile_return(function_return)

    if debug_mode:
        print(optimized_code)

    optimized_bytecode = compile(optimized_code, '', 'exec')

    return optimized_bytecode
