# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: 3600594
"""

from ore_algebra import *
from dfin_op import *
from sage.calculus.var import var
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
    #print L
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
    if(length_IC>=n):
        #print "IC:",diff_eq.get_init_cond()[:n+1]
        return diff_eq.get_init_cond()[:n+1]
    else:
        CI=diff_eq.get_init_cond()
        L=diff_eq.coefficients()
        CI=CI+[calc_sum_func(L,CI,diff_eq.get_x0())]
        x0=diff_eq.get_x0()
        #print "Coef:",L
        #print "P(x)=",L[0]
        #print "P("+str(x0)+")=",L[0](x0)
        #print "Before add IC:",CI
        d=copy(diff_eq.get_diff_eq())
        order_d=d.order()
        while(d.order()!=n):
            d=A('Dx')*d
            #print "Eq after derivation:",d
            L=complete_coeff(d)
            CI=CI+[calc_sum_func(L,CI,x0)]
            #print "CI:",CI
        #print "Coef:",L
        #print "P(x)=",L[0]
        #if(isinstance( L[0], ( int, long,float,complex ) )):
            #print "P("+str(x0)+")=",L[0]
        #else:
            #print "P("+str(x0)+")=",L[0](x0)
        #print "After add IC:",CI
        return CI
       