# -*- coding: utf-8 -*-
"""
Module containing the class ScopLib
"""
from statement import Statement
from condition import Condition
from loop import Loop


class ScopLib:
    """
        Class used to represent a SCoPLib object

        Attributes
        ----------
            language : str
                Language in which this scop was written
            context : tuple
                Context of this scop
            parameters : list
                List of unchanged variables from this scop
            statements : list
                List of all the statements that makes this scop
    """

    def __init__(self, filename=None):
        """
        Instantiates a new Statement with the default values:
            language = None
            context = None
            parameters = empty list
            statements = empty list
        If a file name is provided, it will create a new object with the data of that file

        Parameters
        ----------
            filename=None : path to the SCoPLib file to initialize this object

        Returns
        -------
            A new SCoPLib with values specified in the file or with the default values if a file
            is not provided
        """
        if filename is not None:
            self.__initialize_from_file(filename)
        else:
            self.language = None
            self.context = None
            self.parameters = []
            self.statements = []

    def as_str(self, indentation=0):
        """
        Returns a string that represents the SCoPLib in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain a condition_text as arguments

        Parameters:
        ----------
            indentation=0: the number of tabs at the beginning of the returned

        Returns
        -------
            A string representing the SCoPLib
        """
        string = '\t' * indentation + 'ScopLib:\n'
        string += '\t' * (indentation + 1) + 'Written in :' + str(self.language) + '\n'
        string += '\t' * (indentation + 1) + 'Context in :' + str(self.context) + '\n'
        string += '\t' * (indentation + 1) + 'Parameters :' + ' , '.join(self.parameters) + '\n'
        string += '\t' * (indentation + 1) + 'Statements: \n'
        for statement in self.statements:
            string += statement.as_str(indentation + 2)

        return string

    @staticmethod
    def __generate_scoplib_header(language, context, parameters, number_of_statements):
        """
        Generates the header part of a SCoPLib file represented by this object as a string

        Parameters
        ----------
            language : language of the SCoP represented by the object
            context : context of the SCoP represented by the object
            parameters : list of parameters of the SCoP represented by the object
            number_of_statements : number of statements in the SCoP represented by the object

        Raises
        ------
            ValueError : the context must be a tuple of two values, if it isn't this exception is
            raised

        Returns
        -------
            A string representing the header
        """
        header = '#\n\nSCoP\n\n'
        header += '# ' + '=' * 47 + ' Global\n'
        header += '# Language\n'
        header += '{}\n\n'.format(language)
        header += '# Context\n'
        try:
            header += '{} {}\n\n'.format(context[0], context[1])
        except IndexError:
            raise ValueError('Badly formed context')
        if parameters:
            header += '# Parameter names are provided\n1\n'
            header += '# Parameter names\n'
            header += ' '.join(parameters)
            header += ' \n\n'
        else:
            header += '# Parameter names are not provided\n0\n\n'
        header += '# Number of statements\n{}\n\n'.format(number_of_statements)
        return header

    @staticmethod
    def __generate_scoplib_domain(statement, statement_number, parameters):
        """
        Generates the SCoPLib domain part of a SCoPLib file represented by this object as a string

        Parameters
        ----------
            statement : the statement from which of obtain the domain
            statement_number : the number of the statement in the file
            parameters : list of all the parameters of the SCoPLib

        Returns
        -------
            A string representing the domain
        """
        current_statement = '# ' + '-' * 46 + '  {}.1 Domain\n'.format(statement_number + 1)
        current_statement += '# Iteration domain\n'
        current_statement += '{}\n'.format(1)

        rows = 0
        for loop in statement.loops:
            rows += len(loop.loop_conditions) + len(loop.if_conditions)
        rows += len(statement.if_conditions)
        current_statement += '{} {}\n'.format(rows, 2 + len(statement.loops) + len(parameters))

        conditions = []
        for loop in statement.loops:
            conditions += loop.loop_conditions + loop.if_conditions
        conditions += statement.if_conditions

        for condition in conditions:
            if condition.greater_than:
                current_statement += '{:>4} '.format(1)
            else:
                current_statement += '{:>4} '.format(0)

            for loop2 in statement.loops:
                iterator = '|' + loop2.iterator + '|'
                if iterator in condition.coefficients.keys():
                    current_statement += '{:>4} '.format(condition.coefficients[iterator])
                else:
                    current_statement += '{:>4} '.format(0)

            for param in parameters:
                param = '|' + str(param) + '|'
                if param in condition.coefficients.keys():
                    current_statement += '{:>4} '.format(str(condition.coefficients[param]))
                else:
                    current_statement += '{:>4} '.format(0)

            if condition.term == 0 and not condition.coefficients:
                current_statement += '{:>4} '.format(condition.term)
                current_statement += '   ## {} {} 0\n'.format(condition.string_form(), '>=')
            else:
                current_statement += '{:>4} '.format(condition.term)
                current_statement += '   ## {} {} 0\n'.format(condition.string_form(), '>=')

        return current_statement

    @staticmethod
    def __generate_scoplib_scattering(statement, statement_number, parameters):
        """
            Generates the SCoPLib scattering part of a SCoPLib file represented by this object as
            a string

        Parameters
        ----------
            statement : the statement from which of obtain the domain
            statement_number : the number of the statement in the file
            parameters : list of all the parameters of the SCoPLib

        Returns
        -------
            A string representing the scattering
        """
        current_statement = '# ' + '-' * 46 + '  {}.2 Scattering\n'.format(statement_number + 1)
        if not statement.scattering:
            current_statement += '# Scattering function is not provided\n0\n'
        else:
            current_statement += '# Scattering function is provided\n1\n# Scattering function\n'
            scattering = statement.scattering
            rows = len(scattering) * 2 - 1
            columns = len(scattering) + 1 + len(parameters)
            current_statement += '{} {}\n'.format(rows, columns)

            for _ in range(len(scattering) + len(parameters)):
                current_statement += '{:>4} '.format(0)
            current_statement += '{:>4} '.format(scattering[0][1])  # There's always a level 0
            current_statement += '   ## {}\n'.format(scattering[0][1])
            scattering = scattering[1:]

            scattering_keys = [k[0] for k in scattering]

            for scat in scattering:
                current_statement += '{:>4} '.format(0)
                for j in range(len(scattering)):
                    current_statement += '{:>4} '.format(1 if scat[0] == scattering_keys[j] else 0)
                for _ in parameters:
                    current_statement += '{:>4} '.format(0)
                current_statement += '{:>4} '.format(0)
                current_statement += '   ## {}\n'.format(scat[0].replace('|', ''))

                current_statement += '{:>4} '.format(0)
                for _ in scattering:
                    current_statement += '{:>4} '.format(0)
                for _ in parameters:
                    current_statement += '{:>4} '.format(0)
                current_statement += '{:>4} '.format(scat[1])
                current_statement += '   ## {}\n'.format(scat[1])

            current_statement += '\n'
        return current_statement

    @staticmethod
    def __generate_var(variable, loops, parameters):
        """
        Generates a string representing a tuple in the access format of SCoPLib

        Parameters
        ----------
            variable : the variable_string to analyze
            loops : list of the loops that encapsulates this variable_string
            parameters : list of parameters in the SCoPLib

        Returns
        -------
            The string that represents the variable_string as a string

        """
        result = ''
        if variable.index:
            for i, index in enumerate(variable.index):
                # First polynom_string has the variable_string number, the rest a 0
                if i == 0:
                    result += '{:>4} '.format(variable.number)
                else:
                    result += '{:>4} '.format(0)

                for loop in loops:
                    key = '|' + str(loop.iterator) + '|'
                    if key in index.coefficients.keys():
                        result += '{:>4} '.format(index.coefficients[key])
                    else:
                        result += '{:>4} '.format(0)

                for param in parameters:
                    key = '|' + str(param) + '|'
                    if key in index.coefficients.keys():
                        result += '{:>4} '.format(index.coefficients[key])
                    else:
                        result += '{:>4} '.format(0)

                result += '{:>4} '.format(index.term)

                if i == 0:  # Only first polynom_string has a comment
                    result += '   ##\n'
                else:
                    result += '   ## {}'.format(variable.name.replace('|', ''))
                    for index2 in variable.index:
                        result += '[{}]'.format(index2.string_form())
                    result += '\n'

        else:
            result += '{:>4} '.format(variable.number)
            for i in range(len(loops) + len(parameters) + 1):
                result += '{:>4} '.format(0)
            result += '   ## {}[0]\n'.format(variable.name.replace('|', ''))

        return result

    @staticmethod
    def __generate_scoplib_access(statement, statement_number, parameters):
        """
        Generates the SCoPLib access part of a statement given statement object as a string

        Parameters
        ----------
            statement : the statement from which of obtain the domain
            statement_number : the number of the statement in the file
            parameters : list of all the parameters of the SCoPLib
        """
        current_statement = '# ' + '-' * 46 + '  {}.3 Access\n'.format(statement_number + 1)
        current_statement += '# Access informations are provided\n'
        current_statement += '{}\n'.format(1)
        current_statement += '# Read access informations\n'
        rows = sum((len(v.index) if v.index else 1) for v in statement.read_vars)
        columns = len(statement.loops) + 2 + len(parameters)
        current_statement += '{} {}\n'.format(rows, columns)

        for var in statement.read_vars:
            current_statement += ScopLib.__generate_var(var, statement.loops, parameters)

        current_statement += '# Write access informations\n'
        rows = sum((len(v.index) if v.index else 1) for v in statement.wrote_vars)
        columns = len(statement.loops) + 2 + len(parameters)
        current_statement += '{} {}\n'.format(rows, columns)

        for var in statement.wrote_vars:
            current_statement += ScopLib.__generate_var(var, statement.loops, parameters)

        current_statement += '\n'

        return current_statement

    @staticmethod
    def __generate_scoplib_body(statement, statement_number):
        """
        Generates the SCoPLib body part of a statement given statement object as a string

        Parameters
        ----------
            statement : the statement from which of obtain the domain
            statement_number : the number of the statement in the file
        """
        current_statement = '# ' + '-' * 46 + '  {}.4 Body\n'.format(statement_number + 1)
        current_statement += '# Statement body is provided\n'
        current_statement += '{}\n'.format(1 if statement.code else 0)
        current_statement += '# Original iterator names\n'
        for name in statement.original_iterator_names:
            current_statement += '{} '.format(name.replace('|', ''))
        current_statement += '\n# Statement body\n'
        current_statement += '{};\n\n\n'.format(statement.code)
        return current_statement

    @staticmethod
    def __generate_scoplib_options():
        """
        Generates the SCoPLib body part of a statement given statement object as a string

        Returns
        ------
            None
        """
        current_statement = '# ' + '=' * 47 + ' Options\n'

        return current_statement

    def file_representation(self):
        """
        Returns the contents of a .scop file from the current instance
        """
        scoplib = ScopLib.__generate_scoplib_header(self.language, self.context,
                                                    self.parameters, len(self.statements))

        for i, statement in enumerate(self.statements):
            current_statement = '# ' + '=' * 47 + ' Statement {}\n'.format(i + 1)
            current_statement += ScopLib.__generate_scoplib_domain(statement, i, self.parameters)
            current_statement += ScopLib.__generate_scoplib_scattering(statement,
                                                                       i, self.parameters)
            current_statement += ScopLib.__generate_scoplib_access(statement, i, self.parameters)
            current_statement += ScopLib.__generate_scoplib_body(statement, i)
            scoplib += current_statement

        scoplib += ScopLib.__generate_scoplib_options()

        return scoplib

    @staticmethod
    def __calculate_iteration_domain(statement, params, matrix, columns):
        """
            Establishes the loops of a given statement from a matrix corresponding to the SCoPLib
            domain from a .scop file

        Parameters
        ----------
        statement : the statement to assign the loops
        params : the list of parameters for the .scop file
        matrix : the matrix of the SCoPLib domain from a .scop file as a list of lists
        columns : the number of columns of the matrix

        Returns
        -------
            None
        """
        number_of_loops = columns - 2 - len(params)

        loops = []
        for tup in matrix:
            d_loop = dict()
            d_loop['tup'] = tup
            d_loop['p_tup'] = list(filter(lambda c: c != '', tup.split(' ')))[:columns]
            d_loop['is_greater_than'] = int(d_loop['p_tup'][0])
            # Last iterator with a coefficient different from 0.
            # This is the less restrictive loop for which this condition_text can belong
            num = 0
            iterators = d_loop['p_tup'][1:1 + number_of_loops]
            for i, value in enumerate(iterators[::-1]):
                if value != '0':
                    num = len(iterators) - i
                    break
            d_loop['for_loop_num'] = num - 1
            loops.append(d_loop)

        statement_loops = []
        for i in range(number_of_loops):
            loop = Loop()
            loop.iterator = 'optimization_iterator_' + str(i)
            statement_loops.append(loop)
        for d_loop in loops:
            condition = Condition()
            coefficients = {}
            for cond in range(number_of_loops):
                if int(d_loop['p_tup'][cond + 1]):
                    itera = 'optimization_iterator_' + str(cond)
                    val = int(d_loop['p_tup'][cond + 1])
                    coefficients[itera] = val

            for cond, _ in enumerate(params):
                if int(d_loop['p_tup'][cond + number_of_loops + 1]):
                    par = params[cond]
                    val = int(d_loop['p_tup'][cond + number_of_loops + 1])
                    coefficients[par] = val

            condition.coefficients = coefficients
            condition.term = int(d_loop['p_tup'][-1])

            if len(statement_loops) == 0:
                statement.if_conditions.append(condition)
            else:
                statement_loops[d_loop['for_loop_num']].loop_conditions.append(condition)

        statement.loops = statement_loops

    @staticmethod
    def __calculate_scattering(statement, matrix, rows):
        """
            Establishes the scattering of a given statement from a matrix corresponding to the
            SCoPLib scattering from a .scop file

        Parameters
        ----------
        statement : the statement to assign the scattering
        matrix : the matrix of the SCoPLib scattering from a .scop file as a list of lists
        rows : the number of rows of the matrix

        Returns
        -------
            None
        """
        scattering = []
        iterator = 'AuxiliarScope'  # First value, represents the base level scope. Always needed
        value = matrix[0][-1]
        scattering.append([iterator, value])
        for i in range(1, rows, 2):
            iterators = matrix[i]
            for j, loop in enumerate(statement.loops):
                if iterators[j] == '1':
                    iterator = loop.iterator

            value = matrix[i + 1][-1]

            scattering.append([iterator, value])
        statement.scattering = scattering.copy()

    @staticmethod
    def __rename_variables(statement, original_names):
        """
            Renames the variables from the placeholder names used to the real names.
        Parameters
        ----------
        statement : the statement to rename the variables
        original_names : the list of the original varible names

        Returns
        -------
            None
        """
        for i, name in enumerate(original_names):
            for scat in statement.scattering:
                if scat[0] == 'optimization_iterator_' + str(i):
                    scat[0] = name
                    break
            for loop in statement.loops:
                if loop.iterator == 'optimization_iterator_' + str(i):
                    loop.iterator = name
                for condition in loop.loop_conditions:
                    var_name = 'optimization_iterator_' + str(i)
                    if var_name in condition.coefficients.keys():
                        condition.coefficients[name] = condition.coefficients.pop(var_name)

    def __initialize_from_file(self, file):
        """
            Instantiates a new SCoPLib object with the contents of the file provided
        Parameters
        ----------
            file :  a .scop file to read from

        Returns
        -------
            A new SCoPLib object with the specified contents

        Raises
        ------
            ValueError : if the file is badly formed
        """
        file_content = []
        for line in open(file):
            # Removes comments and empty lines
            line = line.replace('\n', '')
            if (line.strip() == '') or (line[0] == '#'):
                continue
            else:
                file_content.append(line)

        try:
            pos = 0
            if file_content[pos] != 'SCoP':
                raise Exception('Badly formed SCoPLib file')

            pos += 1
            language = file_content[pos]
            self.language = language

            pos += 1
            rows, columns = [int(x) for x in file_content[pos].split(' ')]
            self.context = (rows, columns)
            if rows > 0:
                pos += rows

            pos += 1
            if file_content[pos] == '1':
                pos += 1
                params = file_content[pos].split(' ')
                params = list(filter(lambda x: x != '', params))  # Quita los espacios en blanco
            else:
                params = []
            self.parameters = params

            pos += 1
            number_of_statements = int(file_content[pos])

            pos += 1
            statements = []
            for _ in range(number_of_statements):
                current_statement = Statement()

                # Statement domain
                has_iteration_domain = int(file_content[pos])

                if has_iteration_domain:
                    pos += 1
                    rows, columns = [int(x) for x in file_content[pos].split(' ')]
                    pos += 1

                    iteration_domain_matrix = file_content[pos:pos + rows]
                    ScopLib.__calculate_iteration_domain(current_statement,
                                                         params, iteration_domain_matrix, columns)
                    pos += rows

                # Scattering
                has_scattering = int(file_content[pos])
                if has_scattering:
                    pos += 1
                    rows, columns = [int(x) for x in file_content[pos].split(' ')]

                    pos += 1
                    scattering_matrix = list(list(filter(lambda x: x != '', x.split(' ')))[1:-2]
                                                    for x in file_content[pos: pos + rows])

                    ScopLib.__calculate_scattering(current_statement, scattering_matrix, rows)

                    pos += rows

                # Access
                # Access part is meaningless when reading
                has_access = int(file_content[pos])
                if has_access:
                    pos += 1
                    read_rows, _ = [int(x) for x in file_content[pos].split(' ')]
                    pos += read_rows

                    pos += 1
                    wrote_rows, _ = [int(x) for x in file_content[pos].split(' ')]
                    pos += wrote_rows

                pos += 1
                # Body
                _ = bool(int(file_content[pos]))

                pos += 1
                # Last position will always be blank
                original_iterator_names = file_content[pos].split(' ')[:-1]
                for name in original_iterator_names:
                    current_statement.original_iterator_names.append(name)

                pos += 1
                body = file_content[pos]
                current_statement.code = body

                ScopLib.__rename_variables(current_statement, original_iterator_names)

                statements.append(current_statement)
                pos += 1

        except ValueError:
            raise ValueError('Failed to read the file')

        self.statements = statements
