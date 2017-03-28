# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: 3600594
"""

from ore_algebra import *
from sage.rings.integer_ring import ZZ
from sage.functions.other import *

class dfin_op(object):

    """Calcul formel sur des solutions d'équations
    différentielles linéaires
        -diff_eq est une equation differentiel
        -init_cond est une liste de conditions initiales de notre fonction
    """

    def __init__(self,diff_eq,init_cond=[]):
        self.__diff_eq = diff_eq
        if(init_cond!=[] and len(init_cond)>=diff_eq.order()):
            self.__init_cond=init_cond
        else:
            raise ValueError,"not enough initial values."

    def get_diff_eq(self):
        return self.__diff_eq

    def set_init_cond(self,init_cond):
        self.__init_cond = init_cond

    def get_init_cond(self):
        return self.__init_cond

    def set_diff_eq(self, diff_eq):
        self.__diff_eq = diff_eq
        
    def order(self):
        return self.__diff_eq().order()

    def degree(self):
        return self.__diff_eq.degree()

    def print_eq(self):
        print ("Dfinite equation:")
        print ("Initiale Conditions:",self.__init_cond)
        print ("Equation:",self.__diff_eq)
        
    def __eq__(self,other):
        return self.__diff_eq==other.get_diff_eq() and self.__init_cond==other.get_init_cond()

    def __add__(self,other):
        """Addition de 2 equa diff"""
        self_init_cond_length=len(self.__init_cond)
        other_init_cond_length=len(other.__init_cond)
        if self_init_cond_length == other_init_cond_length :
            i=0
            newlist =[]
            while(i< other_init_cond_length):
                newlist.append(self.__init_cond[i] + other.__init_cond[i])
                i += 1
            z = dfin_op(self.__diff_eq.lclm(other.get_diff_eq()),newlist)
            return z

        elif (self_init_cond_length > other_init_cond_length) :
            i = self_init_cond_length - other_init_cond_length
            an=other.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
            an_order=an.order()
            L=[0]*an_order
            j=0
            for k in other.get_init_cond():
                L[j]=k
                j+=1
            order=self.__diff_eq.order()
            L=an.to_list(L,order)
            for j in range(i-1,order):
                L[j]=factorial(j)*L[j]
            i=0
            newlist=[]
            while (i < self_init_cond_length):
                #other.__init_cond.append(...)
                newlist.append(self.__init_cond[i] + L[i])
                i += 1
            z0=self.__diff_eq.lclm(other.get_diff_eq())
            l=(z0.order()-len(newlist))
            newlist=newlist+[0]*l
            z = dfin_op(z0,newlist)
            return z
        
        elif (self_init_cond_length < other_init_cond_length) :
            i = other_init_cond_length - self_init_cond_length
            an=self.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
            an_order=an.order()
            L=[0]*an_order
            j=0
            for k in self.get_init_cond():
                L[j]=k
                j+=1
            order=other.__diff_eq.order()
            L=an.to_list(L,order)
            for j in range(i-1,order):
                L[j]=factorial(j)*L[j]
            i=0
            newlist=[]
            while (i < other_init_cond_length):
                #other.__init_cond.append(...)
                newlist.append(other.__init_cond[i] + L[i])
                i += 1
            z0=self.__diff_eq.lclm(other.get_diff_eq())
            l=(z0.order()-len(newlist))
            newlist=newlist+[0]*l
            z = dfin_op(z0,newlist)
            return z

    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        self_init_cond_length=len(self.__init_cond)
        other_init_cond_length=len(other.__init_cond)
        if  self_init_cond_length ==  other_init_cond_length :
            i=0
            newlist =[]
            while(i<  self_init_cond_length):
                newlist.append(self.__init_cond[i] * other.__init_cond[i])
                i+= 1
            z = dfin_op(self.__diff_eq.symmetric_product(other.get_diff_eq()),newlist)

            return z

        elif (self_init_cond_length > other_init_cond_length) :
            i = self_init_cond_length - other_init_cond_length
            an=other.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
            an_order=an.order()
            L=[0]*an_order
            j=0
            for k in other.get_init_cond():
                L[j]=k
                j+=1
            order=self.__diff_eq.order()
            L=an.to_list(L,order)
            for j in range(i-1,order):
                L[j]=factorial(j)*L[j]
            i=0
            newlist=[]
            while (i < self_init_cond_length):
                #other.__init_cond.append(...)
                newlist.append(self.__init_cond[i] + L[i])
                i += 1
            z0=self.__diff_eq.symmetric_product(other.get_diff_eq())
            l=(z0.order()-len(newlist))
            newlist=newlist+[0]*l
            z = dfin_op(z0,newlist)
            return z
        
        elif (self_init_cond_length < other_init_cond_length) :
            i = other_init_cond_length - self_init_cond_length
            an=self.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
            an_order=an.order()
            L=[0]*an_order
            j=0
            for k in self.get_init_cond():
                L[j]=k
                j+=1
            order=other.__diff_eq.order()
            L=an.to_list(L,order)
            for j in range(i-1,order):
                L[j]=factorial(j)*L[j]
            i=0
            newlist=[]
            while (i < other_init_cond_length):
                #other.__init_cond.append(...)
                newlist.append(other.__init_cond[i] + L[i])
                i += 1
            z0=self.__diff_eq.symmetric_product(other.get_diff_eq())
            l=(z0.order()-len(newlist))
            newlist=newlist+[0]*l
            z = dfin_op(z0,newlist)
            return z
            
    def calc_init_con(self,n):
        """Function that calculates the initial condition on an x0 point for the n-th order Dx"""
        if(order<=0):
            return []


