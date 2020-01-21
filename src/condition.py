# -*- coding: utf-8 -*-
"""
Module containing the class Condition
"""
from polynom import Polynom


class Condition(Polynom):
    """
    Class used to represent a condition_text

    Attributes
    ----------
        greater_than : boolean
            Indicates if the condition_text is
            'equals to zero' (False) or 'equals or greater than zero' (True)
        coefficients : dict
            Dictionary in which the keys represent the variables and the value of each key
            represent the coefficient by which that variable_string is multiplied
        term : int
            The term is a special value of coefficient that lacks a key, so its treated as a
            special case
    """
    def __init__(self):
        """
        Instantiates a new Condition with the default values:
            greater_than = True
            coefficients = empty
            term = 0

        Returns
        -------
            A new condition_text with the default values
        """
        super(Condition, self).__init__()
        self.greater_than = True

    def __eq__(self, other):
        """
        Compares itself to another polynom.
        Two polynoms are considered equal when:
            * Their greater_than value is the same
            * Their coefficients are the same and with the same values
            * Their term is the sam

        Parameters
        ----------
            other: A polynom to compare

        Returns
        -------
            True if the conditions are equals. False otherwise
        """
        result = True
        if self.greater_than != other.greater_than:
            result = False
        elif self.coefficients != other.coefficients:
            result = False
        elif self.term != other.term:
            result = False
        return result

    def as_str(self, indentation=0):
        """
        Returns a string that represents the condition_text in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain a condition_text as arguments

        Parameters
        ----------
            indentation : the number of tabs at the beginning of the returned string (default = 0)

        Returns
        -------
            A string representing the condition_text
        """
        string = '\t' * indentation
        string += 'Condition with coefficients' + str(self.coefficients)
        string += ' and term ' + str(self.term)
        if self.greater_than:
            string += ' greater or equal to zero'
        else:
            string += 'equals to zero'
        return string
