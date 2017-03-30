# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: 3600594
"""

from ore_algebra import *
from sage.rings.integer_ring import ZZ
from sage.functions.other import *
from sage.all import *

A = OreAlgebra(QQ['x'], 'Dx')

def complete_coeff(diff_eq):
    """
    This function returns a list with the coefficients of diff_eq
    -diff_eq is a differential of <class 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'>
    """
    type_A=type(A("Dx"))
    if(not(isinstance(diff_eq,type_A))):
        raise ValueError,"Expected 1 argument of type ",type_A
    if(len(diff_eq.coefficients())==diff_eq.order()+1):
        return diff_eq.coefficients()
    L=[0]*(diff_eq.order()+1)
    mp=copy(diff_eq)
    while(mp!=0):
        coef=mp.coefficients()
        L[mp.order()]=coef[-1]
        ch="Dx^"+str(mp.order())
        d=A(ch)
        mp=mp-L[mp.order()]*d
    return L

def calc_sum_func(L,CI,x):
    """
    -L is a list of functions
    -CI is a list of numbers (Initial conditions at x)
    -x the point at which we evaluate the function
    """
    if(len(L)<len(CI)+1):
        raise ValueError,"Incompatible length of L and CI .CI and L must have a length difference of 1"
    t=0
    for i in range(len(L)-1):
        if(isinstance( L[i], ( int, long,float,complex ) )):
            l=L[i]
        else:
            l=L[i](x)
        t+=CI[i]*l
    return -t

def calc_init_con(diff_eq,n):
    """
    Function that calculates the initial condition for Dx^n*f where f is the function that diff_eq describes
    diff_eq is of dfin_op type
    """
    if(not(isinstance(diff_eq,dfin_op)) and not(isinstance(n,int))):
        raise ValueError,"Expected 2 aguments of type dfin_op and int type"
    n=int(n)
    if(n<0):
        raise ValueError,"order is always a positive integer"
    length_IC=len(diff_eq.get_init_cond())
    if(length_IC>n):
        return diff_eq.get_init_cond()[:n+1]
    else:
        CI=diff_eq.get_init_cond()
        L=diff_eq.coefficients()
        CI=CI+[calc_sum_func(L,CI,diff_eq.get_x0())]
        x0=diff_eq.get_x0()
        d=copy(diff_eq.get_diff_eq())
        order_d=d.order()
        while(d.order()!=n):
            d=A('Dx')*d
            L=complete_coeff(d)
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI

class dfin_op(object):

    """Calcul formel sur des solutions d'équations
    différentielles linéaires
        -diff_eq est une equation differentiel
        -init_cond est une liste de conditions initiales de notre fonction
        -et x0 est le point surlequel on definit les conditions initiales
    """
    
    def __init__(self,diff_eq,init_cond,x0=0):
        self.__diff_eq = diff_eq
        self.__x0=x0
        if(init_cond!=[] and len(init_cond)>=diff_eq.order()):
            self.__init_cond=init_cond
        else:
            raise ValueError,"not enough initial values."

    def get_diff_eq(self):
        return self.__diff_eq
    
    def get_x0(self):
        return self.__x0
    
    def set_x0(self,x0):
        self.__x0 = x0

    def set_init_cond(self,init_cond):
        self.__init_cond = init_cond

    def get_init_cond(self):
        return self.__init_cond

    def set_diff_eq(self, diff_eq):
        self.__diff_eq = diff_eq
        
    def order(self):
        return self.__diff_eq.order()

    def degree(self):
        return self.__diff_eq.degree()

    def print_eq(self):
        print ("Dfinite equation:")
        print ("Initiale Conditions at x0="+str(self.__x0)+":",self.__init_cond)
        print ("Equation:",self.__diff_eq)
        
    def __str__(self):
        ch="("+str(self.__diff_eq)+","+str(self.__init_cond)+")"
        return str(ch)
        
    def __eq__(self,other):
        return self.__diff_eq==other.get_diff_eq() and self.__init_cond==other.get_init_cond()
    
    def get_dfin_op(self):
        return (self.__diff_eq,self.__init_cond)
    
    def coefficients(self):
        """
        This function returns a list with the coefficients of diff_eq
        -diff_eq is a differential of <class 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'>
        """
        A = OreAlgebra(QQ['x'], 'Dx')
        L=[0]*(self.__diff_eq.order()+1)
        mp=copy(self.__diff_eq)
        while(mp!=0):
            coef=mp.coefficients()
            L[mp.order()]=coef[-1]
            ch="Dx^"+str(mp.order())
            d=A(ch)
            mp=mp-L[mp.order()]*d
        return L

    def __add__(self,other):
        """Addition de 2 equa diff"""
        newlist =[]
        z0=self.__diff_eq.lclm(other.get_diff_eq())
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] + L2[i])
            i += 1
        z = dfin_op(z0,newlist,self.__x0)
        return z


    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        newlist =[]
        z0=z0=self.__diff_eq.symmetric_product(other.get_diff_eq())
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] * L2[i])
            i += 1
        z = dfin_op(z0,newlist,self.__x0)
        return z