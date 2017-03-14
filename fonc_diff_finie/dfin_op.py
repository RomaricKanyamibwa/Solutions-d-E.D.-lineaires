# -*- coding: utf-8 -*-
"""
Created on Tue Mar 14 14:44:25 2017

@author: 3600594
"""



from ore_algebra import *

class dfin_op:
	
	"""Calcul formel sur des solutions d'équations
	différentielles linéaires
	"""
	
	def __init__(self,diff_eq):
        	self.__diff_eq = diff_eq

	def get_diff_eq(self):
		return self.__diff_eq

	def set_diff_eq(self, diff_eq):
		self.__diff_eq = diff_eq
	

	def print_eq():
		print self.get_diff_eq()
		
