
from string import whitespace
from black import NewLine
from pyparsing import OneOrMore, Word, alphas, alphanums, nums, Group, Char, Optional, srange
import pyparsing as pp 

import pandas as pd


# greet = Word(alphas) + "," + Word(alphas) + "!"
# hello = "Hello, World!"
# print(hello, "->", greet.parseString(hello))




source = """

        I -> S '0'
        S -> 'S' S 

        """
lines = source.split('\n')
source = [s.strip() for s in lines]
source = ' '.join(s for s in source).replace('\t', '  ')



terminal = OneOrMore(Char(srange("[a-z][0-9]")))
non_terminal = OneOrMore(Char(srange("[A-S]"))).set_name('non_terminal')


# Combine(Word(alphas)[...], adjacent=False, join_string=" ")

nonterminal = OneOrMore(Char(alphanums).set_name('hello') )##(Char(alphas) + Char(alphas) + Char(nums))

production = Group(nonterminal).set_name('production') #Word(alphas).set_name('production')


rule = pp.OneOrMore(Word(alphas).set_name('name') + '->' + Group(production) + Optional(whitespace))

print(source)

parser = rule
out = parser.parse_string(source) # [parser.parseString(s) for s in source ]
print(source)
print(out)
print(out.as_dict())
print(out.as_list())