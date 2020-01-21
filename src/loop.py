# -*- coding: utf-8 -*-
"""
Module containing the class Loop
"""


class Loop:
    """
    Class used to represent a loop

    Attributes
    ----------
        iterator : str
            The name of the iterator variable_string of the loop
        loop_conditions: list
            List of Condition objects that restrict the iteration domain
        if_conditions : list
            List of conditions of the if statement under which this loop is under
    """

    def __init__(self):
        """
        Instantiates a new Loop with the default values:
            iterator = None
            loop_conditions = empty list
            if_conditions = empty list
        """
        self.iterator = None
        self.loop_conditions = []
        self.if_conditions = []

    def as_str(self, indentation=0):
        """
        Returns a string that represents the loop in a verbose way for debug purposes.
        The indentation argument is used to add tabs at the beginning, useful when used by objects
        that contain variables as arguments

        Parameters:
        ----------
            indentation : the number of tabs at the beginning of the returned string (default = 0)
        """
        string = "\t" * indentation + "Loop with:\n"
        string += "\t" * (indentation+1) + "Iterator variable_string: "+str(self.iterator)+"\n"

        string += "\t" * (indentation+1) + "Loop conditions: \n"
        for coefficient in self.loop_conditions:
            string += coefficient.as_str(indentation + 2) + "\n"

        string += "\t" * (indentation+1) + "If conditions: \n"
        for coefficient in self.if_conditions:
            string += coefficient.as_str(indentation + 2) + "\n"

        return string

    def __eq__(self, other):
        """
        Compares itself to another loop.
        Two loops are considered equal when:
            * Their iterator is the same
            * Their loop_conditions are equal
            * Their if_conditions are equal

        Parameters:
        ----------
            other: A loop to compare
        """
        result = True
        if self.loop_conditions != other.loop_conditions:
            result = False
        if self.if_conditions != other.if_conditions:
            result = False
        if self.iterator != other.iterator:
            result = False
        return result
