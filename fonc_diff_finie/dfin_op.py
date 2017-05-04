# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017
@author: HAKAM Sophia ,DJERRAB Mohamed, KANYAMIBWA Romaric
"""

from ore_algebra import *
from sage.rings.integer_ring import ZZ
from sage.functions.other import *
from sage.all import *
from ore_algebra.ore_operator import OreOperator, UnivariateOreOperator
from sage.rings.polynomial.polynomial_element import Polynomial
from sage.rings.fraction_field_element import FractionFieldElement #Espace de Fonction rationelle
from sage.rings.rational_field import QQ
from sage.calculus.functional import derivative

K = FractionField(PolynomialRing(QQ, 'x')) #utiliser pour faire le polynome P(x,g(x)) de la composition
A = OreAlgebra(QQ['x'], 'Dx')


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
    if(isinstance(diff_eq.get_diff_eq(),Polynomial)):
        
        L=diff_eq.coefficients()
        x0=diff_eq.get_x0()
        CI=[diff_eq.coefficients()[0](x0)]
        d=copy(diff_eq.get_diff_eq())
        order_d=0
        while(len(CI)-1<n):
            d=A('Dx')*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI
    if(not(isinstance(diff_eq,dfin_op)) and not(isinstance(n,int))):
        raise TypeError,"Expected 2 aguments of type dfin_op and int type"
    n=int(n)
    if(n<0):
        raise ValueError,"order is always a positive integer"
    length_IC=len(diff_eq.get_init_cond())
    if(length_IC>n):
        return diff_eq.get_init_cond()[:n+1]
    else:
        CI=diff_eq.get_init_cond()
        L=diff_eq.coefficients()
        x0=diff_eq.get_x0()
        CI=CI+[calc_sum_func(L,CI,x0)]
        d=copy(diff_eq.get_diff_eq())
        order_d=d.order()
        while(d.order()!=n):
            d=A('Dx')*d
            L=d.list()
            CI=CI+[calc_sum_func(L,CI,x0)]
        return CI

class dfin_op(object):

    """Calcul formel sur des solutions d'équations
    différentielles linéaires
        -diff_eq est une equation differentiel
        -init_cond est une liste de conditions initiales de notre fonction
        -et x0 est le point surlequel on definit les conditions initiales
    """
    
    def __init__(self,diff_eq,init_cond=[],x0=0):
        self.__diff_eq = diff_eq
        self.__x0=x0
        if((isinstance(diff_eq,UnivariateOreOperator))):
            if(len(init_cond)>=diff_eq.order()):#raise an error if diff_eq est une fonction
                self.__init_cond=init_cond
            else:
                raise ValueError,"not enough initial values."
        elif isinstance(diff_eq,Polynomial):
            self.__diff_eq = diff_eq
            self.__x0=x0
            if(init_cond!=[]):
                if diff_eq(x0)!=init_cond[0]:
                    raise ValueError,"Initial conditions incompatible with entered function"
            self.__init_cond=[]
        else:
            raise TypeError,"Incompatible type: expected diff_eq of Polynomial or UnivariateOreOperator type"

    def get_diff_eq(self):
        return self.__diff_eq
    
    def get_x0(self):
        return self.__x0
   
    def get_init_cond(self):
        return self.__init_cond
        
    def order(self):
        if(isinstance(self.__diff_eq,Polynomial)):
            return 0
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
        """
        Tests whether or not 2 functions are equal or not 
        """ 
        if self.__diff_eq==other.get_diff_eq() and self.__init_cond==other.get_init_cond():
            return True
        length=min(len(self.__init_cond),len(other.get_init_cond()))
        if self.__init_cond[:length]!=other.get_init_cond()[:length]:
            return False
        temp_diff=self-other
        L=temp_diff.get_init_cond()
        zeroList=[0]*len(L)
        if((temp_diff.get_diff_eq()==other.get_diff_eq() or self.__diff_eq==temp_diff.get_diff_eq()) and L==zeroList):
            return True
        elif calc_init_con(temp_diff,temp_diff.order()*2)==[0]*(temp_diff.order()*2):
            return True
        elif L!=zeroList:
            return False
        
    def __ne__(self,other):
        return not(self==other)
    
    def get_dfin_op(self):
        return (self.__diff_eq,self.__init_cond)
    
    def coefficients(self):
        """
        This function returns a list with the coefficients of diff_eq
        -diff_eq is a UnivariateOreOperator)
        """
        if(isinstance(self.__diff_eq,Polynomial)):
            return [self.__diff_eq]
        return self.__diff_eq.list()
    
    def __sub__(self,other):
        """Sustraction de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial) or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq-other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z1=-other.get_diff_eq()
            z0=self.__diff_eq.lclm(z1)
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] - L2[i])
            i += 1
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z

    def __add__(self,other):
        """Addition de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial)or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq+other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.lclm(other.get_diff_eq())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] + L2[i])
            i += 1
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z


    def __mul__(self,other):
        """Multiplication de 2 equa diff"""
        if(isinstance(self.__diff_eq,Polynomial) or isinstance(other.__diff_eq,Polynomial)):
            z0=self.__diff_eq*other.get_diff_eq()
            if(isinstance(z0,Polynomial)):
                if(self.__x0!=other.get_x0()):
                    raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
                return dfin_op(z0,[],self.__x0)
        else:
            z0=self.__diff_eq.symmetric_product(other.get_diff_eq())
        newlist =[]
        n=z0.order()
        L1=calc_init_con(self,n-1)
        L2=calc_init_con(other,n-1)
        i=0
        while(i< n):
            newlist.append(L1[i] * L2[i])
            i += 1
        if(self.__x0!=other.get_x0()):
            raise ValueError,"Incompatible initial condition, the initial conditions must be defined on the same point x0"
        z = dfin_op(z0,newlist,self.__x0)
        return z
    
    def get_derivative(self):
        """
        Cette fonction calcule le dfin_op associé à la derive self
        """
        tmp_diff=self.__diff_eq
        tmp_IC=self.__init_cond
        tmp_diff=A('Dx')*tmp_diff
        n=tmp_diff.order()
        tmp_IC=calc_init_con(self,n-1)
        return dfin_op(tmp_diff,tmp_IC,self.__x0)
    
    def composition(self,g):
        """
        Fonction qui retourne la composition de diff_op avec f (fog)
        Pour l'instant la fonction retourne la composition que en forme d'une equation diff et pas comme un dfin_op
        """
        
        if(isinstance(g,Polynomial) or isinstance(g,FractionFieldElement)):
            print("Fraction Field",g)
            x, y = QQ['x','y'].gens()
            P=g(x)-y
            print "P(x,g)=",P(x,g)
            if(P(x,g)==0):
                d=self.__diff_eq.annihilator_of_composition(g)
                print "Composition:",d
            else:
                print "The Result is not a Dfinite function"
            return d
            
        else:
            raise TypeError,"A Polynomial or a Rational function is expected as argument"
            
    
    def coeff_power_series(self,order=10):
        """
        Les coeffiecients de la serie formelle associé à self
        """
        diff_eq=self.__diff_eq
        CI=calc_init_con(self,order-1)
        L=[0]*order
        if(self.__x0==0):
            L[0]=CI[0]
            f=1
            for i in range(1,order):
                f=f*i
                L[i]=CI[i]/f
            return L
        else:
            an=diff_eq.to_S(OreAlgebra(QQ["n"], "Sn")) #Suite de la serie entiere associé à l'equation differentielle 
            an_order=an.order()
            L=an.to_list(CI,order)
            return L
        
    def power_series(self,order=6):
        """
        order: est un entier naturel qui represente l'ordre de developement de la serie entiere
        Cette fonction retourne le developpement en serie  de l'equation differentielle self
        """
        L=self.coeff_power_series(order)
        
        return K(L)
    
    def PolyToDiff(self,P,n = 1,x = 0):
        """
        P: est un polynome
        n: est l'ordre de l'equa diff à construire
        x: est le point x0 surlequel on definira les conditions initiales
        Cette fonction retourne la dfin_op associé au polynome  P dans un point x
        """
        if(isinstance(P,Polynomial)):
            h = copy(P)
            L = [0]*n
            for i in range(n):
                L[i] = P(x)
                tmp=P
                P = P.derivative()
                if(P==0):
                    L=L[:i]
                    n=i
                    P=tmp
                    break
            h=P
            ch = 'Dx^' + str(n)
            z = A(ch) - h
            return dfin_op(z,L,x)
        else:
            raise TypeError,"A Polynomial function is expected as argument"


        
        