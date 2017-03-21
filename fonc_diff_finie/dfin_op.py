# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017

@author: 3600594
"""

from ore_algebra import *

class dfin_op(object):

    """Calcul formel sur des solutions d'équations
    différentielles linéaires
        -diff_eq est une equation differentiel
        -init_cond est une liste de conditions initiales de notre fonction
    """

    def __init__(self,diff_eq,init_cond=[]):
        self.__diff_eq = diff_eq
        self.__init_cond=init_cond

    def get_diff_eq(self):
        return self.__diff_eq

    def set_init_cond(self,init_cond):
        self.__init_cond = init_cond

    def get_init_cond(self):
        return self.__init_cond

    def set_diff_eq(self, diff_eq):
        self.__diff_eq = diff_eq


    def print_eq(self):
        print ("Dfinite equation:")
        print ("Condition Initiale:",self.__init_cond)
        print (self.__diff_eq)

    def __add__(self,other):
        """Addition de 2 equa diff"""   
        if len(self.__init_cond) == len(other.__init_cond) :
            i=0
            newlist =[]
            while(i< len(self.__init_cond)):
                newlist.append(self.__init_cond[i] + other.__init_cond)
            z = dfin_op(self.__diff_eq.lclm(other.get_diff_eq()),newlist)
            return z
        
        elif len(self.__init_cond) > len(other.__init_cond) :
            i = len(self.__init_cond) - len(other.init_cond)
            

    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        if len(self.__init_cond) == len(other.__init_cond) :
            i=0
            newlist =[]
            while(i< len(self.__init_cond)):
                newlist.append(self.__init_cond[i] * other.__init_cond)
            z = dfin_op(self.__diff_eq.symmetric_product(other.get_diff_eq()),newlist)
            return z
        elif len(self.__init_cond) > len(other.__init_cond) :
            i = len(self.__init_cond) - len(other.init_cond)
            
            
       
