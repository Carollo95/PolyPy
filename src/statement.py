# -*- coding: utf-8 -*-
"""
Module containing the class Statement
"""


class Statement:
    """
    Class used to represent a statement

    Attributes
    ----------
        loops : list
            List of Loops that under which scope this statement resides
        if_conditions: list
            List of conditions of the if statement under which scope this statement resides
        read_vars : list
            List of Variables that are read in this statement
        wrote_vars : list
            List of Variables that are written in this statement
        code : str
            Code that represents this statement
        original_iterator_names : list
            List of hte iterators of the loops of this statement
        scattering : list
            List of tuples ('string', 'int') that represents the order of this statement in a
            group of statements
    """

    def __init__(self):
        """
        Instantiates a new Statement with the default values:
            loops = empty list
            if_conditions = empty list
            read_vars = empty list
            wrote_vars = empty list
            code = empty string
            original_iterator_names = empty list
            scattering = empty list

        Returns
        -------
            A new condition_text with the default values
        """
        self.loops = []
        self.if_conditions = []
        self.read_vars = []
        self.wrote_vars = []
        self.code = ''
        self.original_iterator_names = []
        self.scattering = []

    def __eq__(self, other):
        """
        Compares itself to another statement.
        Two polynoms are considered equal when:
            * Their loops are equal
            * Their if_conditions are equal
            * Their read_vars are equal
            * Their wrote_vars are equal
            * Their original_iterator_names are equal
            * Their scattering are equal

        Parameters
        ----------
            other: A statement to compare

        Returns
        -------
            True if the statements are equal. False otherwise
        """
        result = True
        if self.loops != other.loops:
            result = False
        elif self.if_conditions != other.if_conditions:
            result = False
        elif self.read_vars != other.read_vars:
            result = False
        elif self.wrote_vars != other.wrote_vars:
            result = False
        elif self.original_iterator_names != other.original_iterator_names:
            result = False
        elif self.scattering != other.scattering:
            result = False
        return result

    def as_str(self, indentation=0):
        """
        Returns a string that represents the statement in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain a condition_text as arguments

        Parameters:
        ----------
            indentation : the number of tabs at the beginning of the returned string (default = 0)

        Returns
        -------
            A string representing the condition_text
        """
        string = "\t" * indentation + "Statement with:\n"

        string += "\t" * (indentation + 1) + "Loops:\n"
        for loop in self.loops:
            string += loop.as_str(indentation + 2) + "\n"

        string += "\t" * (indentation + 1) + "If conditions:\n"
        for loop in self.if_conditions:
            string += loop.as_str(indentation + 2) + "\n"

        string += "\t" * (indentation + 1) + "Read vars:\n"
        for var in self.read_vars:
            string += var.as_str(indentation + 2) + "\n"

        string += "\t" * (indentation + 1) + "Wrote vars:\n"
        for var in self.wrote_vars:
            string += var.as_str(indentation + 2) + "\n"

        string += "\t" * (indentation + 1) + "Code: " + self.code + "\n"
        string += "\t" * (indentation + 1) + "Original iterator names: "
        string += str(self.original_iterator_names) + "\n"
        string += "\t" * (indentation + 1) + "Scattering: " + str(self.scattering) + "\n"

        return string
