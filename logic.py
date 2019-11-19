import pprint as pp
import re
import copy
import itertools as it
"""
Atomic formula
in p(x,y)
p is the symbol
x,y are args
2 is arity
"""
class Form:
    def __init__(self, symbol, args):
        self.symbol = symbol
        self.args = args #list of args
        self.arity = len(args)
    def __str__(self):
        return (self.symbol + "(" + ", ".join(str(e) for e in self.args) + ")")
    def __repr__(self):
        return (self.symbol + "(" + ", ".join(str(e) for e in self.args) + ")")
    def __eq__(self, other):
        if isinstance(other, Form):
            return self.symbol == other.symbol and self.args == other.args
    def __hash__(self):
        return hash((self.symbol,self.arity))

"""
 Conjunctive Normal Form:
(t1 and t2 and t3)
where terms are of the format:
x1 or x2 or x3

"""
class CNF:
    def __init__(self, terms):
        self.terms = terms
    def __repr__(self):
        return ", ".join(repr(x) for x in self.terms)
    def __getitem__(self,index):
        return self.terms[index]
    def __setitem__(self,index,value):
        self.terms[index] = value
    def variables(self):
        return [x for term in self.terms for x in term.args]

class HornClause:
    def __init__(self, weight, csq, antecedents):
        self.weight = weight
        self.csq = csq # Term, consequent
        self.antecedents = antecedents # List of args, antecedents
    def __repr__(self):
        return str(self.weight) + " " + (repr(self.antecedents) + " => " + repr(self.csq))

"""
Abduction rule
x and y -- z
means that (x and y) is a subset of z
i.e. all things that satisfy (x and y) also satisfy z
"""
class Rule:
    def __init__(self, no, ante, conse):
        self.no = no
        self.ante = ante # List of args, antecedents
        self.conse = conse # Term, consequent
    def __repr__(self):
        reprAnte = [repr(d) for d in self.ante]
        reprConse = [repr(d) for d in self.conse]
        return "Rule (" + str(self.no) + "): " + u' \u2227 '.join(reprAnte) + u' \u2283 ' + u' \u2227 '.join(reprConse)

class customForm:
    def __init__(self, weight, ant, consequents):
        self.weight = weight
        self.ant = ant
        self.consequents = consequents
    def __repr__(self):
        T = ""
        for e in self.consequents:
            truthValue = e[0]
            eVars = e[1]
            terms = CNF(e[2])
            T += "!" if truthValue == 0 else ""
            if eVars:
                T += ''.join(' '.join(x) for x in zip(it.cycle(["EXIST"]), [x+" " for x in eVars]))
            T += repr(terms) + " v "
        T = T[:-3]
        return str(self.weight) + " " + repr(self.ant) + " => " + T

class mutExcForm:
    def __init__(self, ant, consequents):
        self.ant = ant
        self.consequents = consequents
    def __repr__(self):
        mainForm = repr(self.ant) + " => "
        formList = []
        for terms in self.consequents:
            for term in terms:
                formList.append(term)
        return mainForm + "!" + " v !".join(repr(form) for form in formList) + "."

class revImplForm:
    def __init__(self, weight, ant, consequents, no):
        self.weight = weight
        self.ant = ant
        self.consequents = consequents
        #ensuring unique clause numbers
        self.no = no
    def __repr__(self):
        x = len(self.consequents) +1
        partialWeight = self.weight/x
        # mainForm will contain clause #1 (ANT -> C1 v C2 v ... v CN)
        mainForm = str(partialWeight) + " " + repr(self.ant) + " => "
        #resultStr will contain all other clauses
        resultStr = []
        #list of temporary clauses
        tempList = []
        itr = 0
        # for each disjunt in consequents
        for e in self.consequents:
            eVars = e[0]
            terms = CNF(e[1])
            consEx = "EXIST " + ",".join(x for x in eVars) + " " if eVars else ""
            cons =  consEx + repr(terms)
            #create a temporary clause with unique number
            tempForm = f"tempclause(x{self.no+itr})"
            tempList.append(tempForm)
            #create new implication clauses
            resultStr.append(f"{str(partialWeight/2)} {cons} => {tempForm}")
            x = len(terms.terms)
            termWeight = partialWeight/(x*2)
            for term in terms:
                resultStr.append(f"{str(termWeight)} {consEx} {tempForm} => {repr(term)}")
            itr += 1
        mainForm = mainForm + " v ".join(temp for temp in tempList)
        resultStr = [mainForm] + resultStr
        return "\n".join(clause for clause in resultStr)

#String converters
def lispvar(s):
    return isinstance(s, str) and s and s[0] == '?'

def lispconst(s):
    return isinstance(s,str) and bool(re.search(r'\d', s)) and s[0] != '?'

def tuffvar(s):
    return isinstance(s,str) and s.islower()

def tuffconst(s):
    return isinstance(s,str) and s.istitle()

def lisptotuff(s):
    if lispvar(s):
        return s[1:]
    elif lispconst(s):
        return s.title()
    print("ERROR")
    return False

def symb(s):
    return s.lower() and s[0] != '?' and bool(re.search(r'\d', s)) == 0

def posCheck(m, R):
    for i in range(m.arity):
        if (tuffconst(R.args[i]) and tuffvar(m.args[i])):
            return False
    return True

def unifiable(pred1, pred2):
    if isinstance(pred1, Form) and isinstance(pred2, Form):
        return (pred1.symbol == pred2.symbol) and (pred1.arity == pred2.arity)
    if tuffconst(pred1) and tuffconst(pred2):
        return False
    return True

def unify(a,b,theta):
    a = theta[a] if a in theta else a
    b = theta[b] if b in theta else b
    if(a == b):
        return theta
    if (tuffvar(a) and tuffvar(b)):
        if a<=b:
            theta[a] = b
        else:
            theta[b] = a
        return theta
    if tuffvar(a):
        theta[a] = b
        return theta
    elif tuffvar(b):
        theta[b] = a
        return theta
    #a and b are constants
    print("ERROR: ATTEMPT AT UNIFYING TWO DIFFERENT CONSTANTS" + a + " " + b)
    return theta

def unified(term,theta):
    newTerm = copy.deepcopy(term)
    for i in range(newTerm.arity):
        newTerm.args[i] = theta[newTerm.args[i]] if newTerm.args[i] in theta else newTerm.args[i]
    return newTerm

def unifyTerms(term1, term2):
    if not unifiable(term1, term2):
        return False
    theta = dict()
    for i in range(len(term1.args)):
        theta = unify(term1.args[i], term2.args[i], theta)
    return theta

def predPattern(predicate):
    if isinstance(predicate, Form):
        return Form(predicate.symbol, ['?' for i in range(predicate.arity)])
    print("EXPECTED: Form; RECEIVED: " + predicate)
    return False

def sort(x1, x2):
    if x1 == x2:
        return False
    return (x1, x2) if x1.args <= x2.args else (x2, x1)
