# -*- coding: utf-8 -*-
"""
Module containing the class Polynom
"""


class Polynom:
    """
    Class used to represent a polynom

    Attributes
    ----------
        coefficients : dict
            Dictionary in which the keys represent the variables and the value of wach key
            represent the coficient by which that variable_string is multiplied
        term : int
            The term is a special value of coeficient that lacks a key, so its treated as a
            special case
    """

    def __init__(self):
        """
        Instantiates a new Polynom with the default values:
            coefficients = empty
            term = 0

        Returns
        -------
            A new polynom with the default values
        """
        self.coefficients = {}
        self.term = 0

    def __eq__(self, other):
        """
        Compares itself to another polynom.
        Two polynoms are considered equal when:
            * Their coeficients are the same and with the same values
            * Their term is the sam

        Parameters
        ----------
            other: A polynom to compare

        Returns
        -------
            True if the polynoms are equal. False otherwise
        """
        result = True
        if self.coefficients != other.coeficients:
            result = False
        elif self.term != other.term:
            result = False
        return result

    def string_form(self):
        """
        Returns a string that represents the polynom as a mathematical expression.

        Returns
        -------
            A string representing the polynom as a mathematical expression
        """
        string = ''
        aux = []

        for key in self.coefficients:
            if self.coefficients[key] != 0:
                if self.coefficients[key] == 1:
                    aux.append(str(key).replace('|', ''))
                else:
                    aux.append(str(key).replace('|', '') + '*' + str(self.coefficients[key]))

        string += '+'.join(aux)

        if self.term != 0:
            if self.term > 0:
                string += '+'
            string += str(self.term)

        return string

    def as_str(self, indentation=0):
        """
        Returns a string that represents the polynom in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain polynoms as arguments

        Parameters
        ----------
            indentation=0: the number of tabs at the beginning of the returned string

        Returns
        -------
            A string representing the condition_text
        """
        string = '\t' * indentation
        string += 'Polynom with coefficients' + str(self.coefficients)
        string += ' and term ' + str(self.term)
        return string
