# -*- coding: utf-8 -*-
"""
Module containing the class Variable
"""


class Variable:
    """
    Class used to represent a variable_string

    Attributes
    ----------
        name : str
            The name of the variable_string
        number: int
            Id number asociated with this particular variable_string. Several instances of the variable_string
            object may exist with the same id only if they represent different instances of the
            same variable_string
        index : list
            List of all the indexes of the variable_string when the variable_string object represents an element
            of a list. Each one of them represents a dimension of the list when the list is
            multidimensional
        index_text : str
            Representation of the indexes as a list
    """

    def __init__(self, name, number):
        """
        Instantiates a new Variable with the default values:
            polynom_string : an empty list
            index_text : an empty string

        Parameters
        ----------
            name : name of the new Variable
            number : number id of the new Variable

        Returns
        -------
            A new variable_string with the default values
        """
        self.name = name
        self.number = number
        self.index = []
        self.index_text = ''

    def __lt__(self, other):
        """
        Compares itself to another variable_string
        True when this variable_string's, number is less than the other variable_string's number

        Parameters
        ----------
            other : a variable_string to compare

        Returns
        -------
            True if this instance's number is less than the others
        """
        return self.number < other.number

    def as_str(self, indentation=0):
        """
        Returns a string that represents the variable_string in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain variables as arguments

        Parameters
        ----------
            indentation : the number of tabs at the beginning of the returned string (default = 0)

        Returns
        -------
            A string representing the condition_text
        """
        string = '\t' * indentation + 'Variable with:\n'
        string += '\t' * (indentation + 1) + 'Name:  ' + str(self.name) + '\n'
        string += '\t' * (indentation + 1) + 'Number: ' + str(self.number) + '\n'
        string += '\t' * (indentation + 1) + 'Index: ' + '\n'
        for pol in self.index:
            string += pol.as_str(indentation + 2) + '\n'
        string += '\t' * (indentation + 1) + 'Index text: ' + self.index_text + '\n'
        return string
