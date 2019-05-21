from timeit import default_timer as timer
from itertools import combinations, permutations
from collections.abc import Iterable
from z3 import Solver, sat, Real, RealSort, BoolSort, Not, Or
def grt(lhs, rhs):
    return lhs.evaluate() > rhs.evaluate()

def grteql(lhs, rhs):
    return lhs.evaluate() >= rhs.evaluate()

def sml(lhs, rhs):
    return lhs.evaluate() < rhs.evaluate()

def smleql(lhs, rhs):
    return lhs.evaluate() <= rhs.evaluate()

def eql(lhs, rhs):
    #if (not lhs.isConstant) and (not rhs.isConstant) and (lhs.id == rhs.id):
    if lhs.id == rhs.id:
        #lhs and rhs are the same symbol
        return True
    else:
        return lhs.evaluate() == rhs.evaluate()

def neql(lhs, rhs):
    if (lhs.isConstant) and (rhs.isConstant) and (lhs.value != rhs.value):
        #lhs and rhs are different constants
        return True
    else:
        return lhs.evaluate() != rhs.evaluate()

comparisonFun = {'=':eql, '!=':neql, '>':grt, '>=':grteql, '<':sml, '<=':smleql}

def plus(lhs, rhs):
    return lhs.evaluate() + rhs.evaluate()

def minus(lhs, rhs):
    return lhs.evaluate() - rhs.evaluate()

def multiply(lhs, rhs):
    return lhs.evaluate() * rhs.evaluate()

def divide(lhs, rhs):
    return lhs.evaluate() / rhs.evaluate()

arithmeticFun = {'+': plus, '-': minus, '*': multiply, '/': divide}

class MySymbol(object):
    """
    A symbol can either be a constant or a variable.
    If the symbol is a variable, the value must be a string type.
    If the symbol is a constant, value can either be a numeric type, a string type, or a tuple of numeric or string type.
    """
    symbolIdDict = {}
    def __init__(self, value, isConstant):
        if (isConstant):
            #if isinstance(value, tuple):
            #    assert all(isinstance(x, int) for x in value) or all(isinstance(x, float) for x in value) or all(isinstance(x, str) for x in value) , "Invalid value ({}) for constant symbol.".format(value)
            #else:
            #    assert isinstance(value, (int, float, str))
            assert isinstance(value, (int, float, str)), "Invalid value ({}) for constant MySymbol. The value of a constant must be numeric or string type.".format(value)
        else:
            assert isinstance(value, str), "Invalid value ({}) for variable symbol. The value of a variable must be string type.".format(value)

        if (value, isConstant) in self.symbolIdDict:
            self.id = self.symbolIdDict[(value, isConstant)]
        else:
            self.id = len(self.symbolIdDict)
            self.symbolIdDict[(value, isConstant)] = self.id
        self.isConstant = isConstant
        self.value = value

    def __add__(self, other):
        return Plus(self, other)
    
    def __sub__(self, other):
        return Subtract(self, other)
    
    def __mul__(self, other):
        return Multiply(self, other)

    def __truediv__(self, other):
        return Divide(self, other)

    def __lt__(self, other):
        return Sml(self, other)

    def __gt__(self, other):
        return Grt(self, other)

    def __le__(self, other):
        return SmlEql(self, other)

    def __ge__(self, other):
        return GrtEql(self, other)

    def __eq__(self, other):
        return Equal(self, other)

    def __ne__(self, other):
        return NEqual(self, other)

    def evaluate(self):
        """Convert symbol to either a constant or a z3 Real type object."""
        if isinstance(self.value, (int, float)):
            return self.value
        else:
            return Real(self.show())

    def show(self):
        if self.isConstant:
            if isinstance(self.value, str):
                return '\'{}\''.format(self.value)
            else:
                return '{}'.format(self.value)
        else:
            return self.value

class Constant(MySymbol):
    def __init__(self, value):
        assert isinstance(value, (int, float)), "Invalid value ({}) for Constant. The value of a constant must be numeric type.".format(value)
        MySymbol.__init__(self, value, True)

class Variable(MySymbol):
    def __init__(self, value):
        MySymbol.__init__(self, value, False)

class ExpansionSymbol(Variable):
    def __init__(self, name, expandFrom):
        Variable.__init__(self, name)
        self.expandFrom = expandFrom

class VariableExpansion(ExpansionSymbol):
    expansionCntDict = {}
    def __init__(self, expandFrom):
        assert not expandFrom.isConstant
        self.expansionCntDict[expandFrom.id] = self.expansionCntDict.get(expandFrom.id, 0) + 1
        name = f'{expandFrom.value}Ex{self.expansionCntDict[expandFrom.id]}'
        ExpansionSymbol.__init__(self, name, expandFrom)

class ConstantExpansion(ExpansionSymbol):
    expansionCnt = 0
    def __init__(self, expandFrom):
        assert expandFrom.isConstant
        ConstantExpansion.expansionCnt += 1
        name = f'cnstEx{self.expansionCnt}'
        ExpansionSymbol.__init__(self, name, expandFrom)

class FunctionExpansion(ExpansionSymbol):
    expansionCntDict = {}
    def __init__(self, expandFrom):
        assert isinstance(expandFrom, FunctionSymbol)
        self.expansionCntDict[expandFrom.id] = self.expansionCntDict.get(expandFrom.id, 0) + 1
        name = f'{expandFrom.value}Ex{self.expansionCntDict[expandFrom.id]}'
        ExpansionSymbol.__init__(self, name, expandFrom)

class GroundSymbol(Constant):
    def __init__(self, groundedFrom):
        assert not groundedFrom.isConstant
        name = f'{groundedFrom.value}Gnd'
        MySymbol.__init__(self, name, True)
        #Constant.__init__(self, name)
        self.groundedFrom = groundedFrom

class Predicate(object):
    _PREDICATE_LIST = ['bogus', '=', '!=', '>', '<=', '<', '>='] # we use a bogus predicate to take up predicate id 0
    _ARG_NUM_LIST = [0, 2, 2, 2, 2, 2, 2]
    predicateIdDict = {'Null':0, '=':1, '!=':2, '>':3, '<=':4, '<':5, '>=':6} # FIX ME: the arithmetic operators won't have their opposite ones, making arithmetic operators as predicates is probably not a good choice. Shall make an arithmetic expression return a symbol in the future
    _PREDICATE_ID_BASE = 3
    _BUILTIN_PREDICATE_NUMBER = 7

    def __init__(self, name, argumentList, negated = False):
        self._ARGUMENTS = []
        self._ARGTAGS = []
        self.substitutionTag = 0
        self.expandTo = []
        # a predicate instance is initiated by its name, and a list of its argument. Each element in the argument list should be a MySymbol object.
        self.name = name
        if name in self.predicateIdDict:
            self.id = self.predicateIdDict[name]
            assert self.argNum == len(argumentList), "predicate \'{}\' passed invalid number of arguments: {}".format(name, [s.show() for s in argumentList])
        else:
            self.id = len(self._PREDICATE_LIST)
            self._PREDICATE_LIST.append(name)
            self._ARG_NUM_LIST.append(len(argumentList))
            #self.id = len(self._PREDICATE_LIST) - self._BUILTIN_PREDICATE_NUMBER + self._PREDICATE_ID_BASE
            self.predicateIdDict[name] = self.id

            #construct a z3 function for the new predicate
            #predicate2Z3Fun[name] = Function(name, [RealSort()] * len(argumentList) + [BoolSort()])

        self.argIdx = {} # argIdx maps a symbol id to a list of indices where the symbol appears in the literal
        for arg in argumentList:
            if not isinstance(arg, MySymbol):
                arg = Constant(arg)
            if arg.id in self.argIdx:
                self.argIdx[arg.id].append(len(self._ARGUMENTS))
            else:
                self.argIdx[arg.id] = [len(self._ARGUMENTS)]
            self._ARGUMENTS.append([arg])
            self._ARGTAGS.append([self.substitutionTag])

        if negated:
            self.id = -self.id

    @property
    def arguments(self):
        return [argStack[-1] for argStack in self._ARGUMENTS]

    @property
    def isNegated(self):
        return self.id < 0

    def argumentAt(self, idx):
        """Return current argument at position idx."""
        return self._ARGUMENTS[idx][-1]

    def negate(self):
        self.id = -self.id
        return self

    @property
    def argNum(self):
        return self._ARG_NUM_LIST[abs(self.id)]

    def replace(self, replacingSym, replacingIdx):
        """Replace the argument at the position replaceIdx with the symbol replacingSym."""
        replacedArgId = self.argumentAt(replacingIdx).id
        replacedArgAllPosition = self.argIdx[replacedArgId]

        # update argument stack
        self._ARGUMENTS[replacingIdx].append(replacingSym)
        self._ARGTAGS[replacingIdx].append(self.substitutionTag)

        # update argument index
        replacedArgAllPosition.remove(replacingIdx)
        if len(replacedArgAllPosition) == 0:
            self.argIdx.pop(replacedArgId)
        if replacingSym.id not in self.argIdx:
            self.argIdx[replacingSym.id] = [replacingIdx]
        else:
            self.argIdx[replacingSym.id].append(replacingIdx)

    def substitute(self, replacingSym, replacedSym):
        """Substitute the symbol replacedSym with the symbol replacingSym."""
        replacedArgId = replacedSym.id
        if (replacedArgId not in self.argIdx):
            return
        else:
            replacedArgAllPosition = self.argIdx[replacedArgId]

        # update argument stack
        for replacingIdx in replacedArgAllPosition:
            self._ARGUMENTS[replacingIdx].append(replacingSym)
            self._ARGTAGS[replacingIdx].append(self.substitutionTag)

        # update argument index
        self.argIdx.pop(replacedArgId)
        if replacingSym.id not in self.argIdx:
            self.argIdx[replacingSym.id] = replacedArgAllPosition
        else:
            self.argIdx[replacingSym.id] += replacedArgAllPosition

    def undo_substitution(self, tag = None):
        """Undo all the substitutions with a substitution tag greater than a given tag or equal to current substitution tag."""
        if self.substitutionTag == 0:
            return
        if tag:
            #assert tag < self.substitutionTag
            if tag >= self.substitutionTag: 
                return
            else:
                self.substitutionTag = tag
        else:
            self.substitutionTag -= 1

        argIdxMinus = {}
        argIdxPlus= {}
        for i in range(len(self._ARGUMENTS)):
            argStack = self._ARGUMENTS[i]
            tagStack = self._ARGTAGS[i]
            if tagStack[-1] > self.substitutionTag:
                if argStack[-1].id in argIdxMinus:
                    argIdxMinus[argStack[-1].id].append(i)
                else:
                    argIdxMinus[argStack[-1].id] = [i]

                while tagStack[-1] > self.substitutionTag:
                    tagStack.pop()
                    argStack.pop()

                if argStack[-1].id in argIdxPlus:
                    argIdxPlus[argStack[-1].id].append(i)
                else:
                    argIdxPlus[argStack[-1].id] = [i]

        # update argument index
        for k in argIdxMinus:
            for idx in argIdxMinus[k]:
                self.argIdx[k].remove(idx)
        for k in argIdxPlus:
            if k in self.argIdx:
                self.argIdx[k] += argIdxPlus[k]
            else:
                self.argIdx[k] = argIdxPlus[k]
        for k in [k for k in self.argIdx]:
            if len(self.argIdx[k]) == 0:
                self.argIdx.pop(k)

    def show(self):
        out = f"{self.name}("
        for arg in self._ARGUMENTS:
            out += f"{arg[-1].show()}, "
        out = out[:-2]
        out += ")"
        return out

    def copy(self):
        return Predicate(self.name, self.arguments, negated=self.isNegated)

class NullPredicate(Predicate):
    """A null predicate used for head when it is empty."""
    def __init__(self):
        Predicate.__init__(self, 'Null', [])
    
    def copy(self):
        return NullPredicate()

    def show(self):
        return ''

class ComparisonPredicate(Predicate):
    def __init__(self, name, lhs, rhs):
        Predicate.__init__(self, name, [lhs, rhs])

    @property
    def lhs(self):
        return self._ARGUMENTS[0][-1]

    @property
    def rhs(self):
        return self._ARGUMENTS[1][-1]

    def show(self):
        return f"{self._ARGUMENTS[0][-1].show()} {self.name} {self._ARGUMENTS[1][-1].show()}"

    def copy(self):
        ret = ComparisonPredicate(self.name, self.lhs, self.rhs)
        if self.isNegated:
            ret.negate()
        return ret

    def evaluate(self):
        return comparisonFun[self.name](self.lhs, self.rhs)

class Equal(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '=', lhs, rhs)
    
    def negate(self):
        self.name = '!='
        self.id = Predicate.predicateIdDict[self.name]

    def copy(self):
        return Equal(self.lhs, self.rhs)

class NEqual(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '!=', lhs, rhs)

    def negate(self):
        self.name = '='
        self.id = Predicate.predicateIdDict[self.name]

    def copy(self):
        return NEqual(self.lhs, self.rhs)

class Grt(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '>', lhs, rhs)

    def negate(self):
        self.name = '<='
        self.id = Predicate.predicateIdDict[self.name]
    
    def copy(self):
        return Grt(self.lhs, self.rhs)

class GrtEql(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '>=', lhs, rhs)

    def negate(self):
        self.name = '<'
        self.id = Predicate.predicateIdDict[self.name]

    def copy(self):
        return GrtEql(self.lhs, self.rhs)

class Sml(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '<', lhs, rhs)

    def negate(self):
        self.name = '>='
        self.id = Predicate.predicateIdDict[self.name]

    def copy(self):
        return Sml(self.lhs, self.rhs)

class SmlEql(ComparisonPredicate):
    def __init__(self, lhs, rhs):
        ComparisonPredicate.__init__(self, '<=', lhs, rhs)

    def negate(self):
        self.name = '>'
        self.id = Predicate.predicateIdDict[self.name]
    
    def copy(self):
        return SmlEql(self.lhs, self.rhs)

class ExpansionPredicate(Equal):
    def __init__(self, lhs, rhs, expandFrom):
        Equal.__init__(self,lhs, rhs)
        self.expandFrom = expandFrom

    def copy(self):
        ret = ExpansionPredicate(self.lhs, self.rhs, self.expandFrom)
        if self.isNegated:
            ret.negate()
        return ret

class Function(Predicate):
    """
    Although this class inherits from Predicates class, this is only for convenience, as a Function object is actually a function expression.
    """
    functionDict = {**comparisonFun, **arithmeticFun}
    def __init__(self, name, argumentList):
        Predicate.__init__(self, name, argumentList)

    def substitute(self, replacingSym, replacedSym):
        for arg in self.arguments:
            if isinstance(arg, FunctionSymbol):
                arg.function.substitute(replacingSym, replacedSym)
        Predicate.substitute(self, replacingSym, replacedSym)
    
    def evaluate(self):
        return self.functionDict[self.name](*self.arguments)

class FunctionSymbol(MySymbol):
    cntDict = {}
    def __init__(self, functionName, argumentList):
        self.functionName = functionName
        self.function = Function(self.functionName, argumentList)
        self.argCnt = {}
        for arg in argumentList:
            if not isinstance(arg, FunctionSymbol):
                self.argCnt[arg.id] = self.argCnt.get(arg.id, 0) + 1
            else:
                for ak in arg.argCnt:
                    self.argCnt[arg.id] = self.argCnt.get(arg.id, 0) + arg.argCnt[ak]
        self.cntDict[self.functionName] = self.cntDict.get(self.functionName, 0) + 1
        MySymbol.__init__(self, f'{self.functionName}{self.cntDict[functionName]}', False)

    def evaluate(self):
        return self.function.evaluate()

    def show(self):
        return self.function.show()

class BinaryOperator(FunctionSymbol):
    def __init__(self, operator, lhs, rhs):
        self.operator = operator
        FunctionSymbol.__init__(self, self.operator, [lhs, rhs])

    @property
    def lhs(self):
        return self.function._ARGUMENTS[0][-1]

    @property
    def rhs(self):
        return self.function._ARGUMENTS[1][-1]

    def show(self):
        return f'({self.lhs.show()} {self.operator} {self.rhs.show()})'

class Plus(BinaryOperator):
    def __init__(self, lhs, rhs):
        BinaryOperator.__init__(self, '+', lhs, rhs)

class Subtract(BinaryOperator):
    def __init__(self, lhs, rhs):
        BinaryOperator.__init__(self, '-', lhs, rhs)

class Multiply(BinaryOperator):
    def __init__(self, lhs, rhs):
        BinaryOperator.__init__(self, '*', lhs, rhs)

class Divide(BinaryOperator):
    def __init__(self, lhs, rhs):
        BinaryOperator.__init__(self, '/', lhs, rhs)

class PredicateSet(object):
    """
    A set of predicates in conjunction or disjunction, each predicate may or may not be negated.
    """
    def __init__(self, predicates, conjunction = True):
        self.isConjunction = conjunction
        self.predicateIdxDict = {}
        self.predicates = []
        self.substitutionTag = 0

        if isinstance(predicates, Iterable):
            for predicate in predicates:
                self.add_predicate(predicate)
        else:
            self.add_predicate(predicates)

    def __getitem__(self, key):
        return self.predicates[key]

    def __iter__(self):
        for p in self.predicates:
            yield p

    def __len__(self):
        return len(self.predicates)

    def add_predicate(self, predicate):
        self.predicates.append(predicate)
        predicateIdx = len(self.predicates)
        if predicate.id in self.predicateIdxDict.keys():
            self.predicateIdxDict[predicate.id].append(predicateIdx)
        else:
            self.predicateIdxDict[predicate.id] = [predicateIdx]
    
    #def sort(self):
    #    self.predicates = sorted(self.predicates, key=lambda predicate:predicate.id)
    
    def negate(self):
        for p in self.predicates:
            p.negate()
        self.isConjunction = not self.isConjunction
        return self

    def copy(self):
        return PredicateSet([p.copy() for p in self.predicates], self.isConjunction)

    def show(self, conjunctConnector = ' And ', disjunctConnector = ' Or '):
        if len(self.predicates) == 0:
            return ''
        if self.isConjunction:
            connector = conjunctConnector
        else:
            connector = disjunctConnector

        out = ''
        for i, p in enumerate(self.predicates):
            out += p.show()
            if i < len(self.predicates) - 1:
                out += connector
        return out

class Rule(PredicateSet):
    """
    A datalog rule that has the form h :- b1, b2, .., bn.
    """
    def __init__(self, head = None, body = None):
        if head is None:
            head = NullPredicate()
        self.head = head
        self.functions = []
        PredicateSet.__init__(self, body)
        self.body = self.predicates

        # statistics
        self.z3Time = 0
        self.z3InvokedTimes = 0
        self.searchTime = 0
        self.totalRunTime = 0
    
    def __getitem__(self, key):
        if key == 0:
            return self.head
        else:
            return PredicateSet.__getitem__(self, key-1)

    def __iter__(self):
        yield self.head
        for p in self.predicates:
            yield p

    def __len__(self):
        if isinstance(self.head, NullPredicate):
            return len(self.predicates)
        else:
            return len(self.predicates) + 1

    def add_predicate(self, predicate):
        PredicateSet.add_predicate(self, predicate)
        for arg in predicate.arguments:
            if isinstance(arg, FunctionSymbol):
                self._add_function(arg, predicate)

    def _add_function(self, funcSym, expandFrom):
        #PredicateSet.add_predicate(self, ExpansionPredicate('=', FunctionExpansion(funcSym), funcSym, expandFrom))
        self.functions.append(ExpansionPredicate(FunctionExpansion(funcSym), funcSym, expandFrom))
        self.functions.append(funcSym.function)
        for arg in funcSym.function.arguments:
            if isinstance(arg, FunctionSymbol):
                self._add_function(arg, funcSym.function)

    def match_predicate(self, predicateIdx, targetPredicate):
        """
        This function tries to match the predicate at predicateIdx with targetPredicate by substituting variables. 
        If success, a substitution list is returned, otherwise None is returned.
        The two predicates must have different variable symbols.
        """
        if self.predicates[predicateIdx].id != targetPredicate.id:
            return False
        self.substitutionTag += 1
        matchingArgs = self.predicates[predicateIdx].arguments
        targetArgs = targetPredicate.arguments
        for matchingArg, targetArg in zip(matchingArgs, targetArgs):
            if matchingArg.isConstant:
                if matchingArg != targetArg:
                    self.undo_substitution()
                    return False
            elif type(matchingArg) == ConstantExpansion and type(targetArg) == Constant:
                # if we know that the matching symbol is an expansion symbol from a constant, and the target symbol is also a constant (not a constant from ground instantiation), then we can check if the two constants are equal, to avoid further unnecessary matchings
                if matchingArg.expandFrom != targetArg:
                    self.undo_substitution()
                    return False
                else:
                    self.substitute(targetArg, matchingArg)
            else:
                self.substitute(targetArg, matchingArg)
                if type(matchingArg) == VariableExpansion and type(targetArg) == Constant:
                    # if we know that the matching symbol is an expansion symbol from a variable, and the target symbol is also a constant (not a constant from ground instantiation), then we can check if the matching will make the equality predicate for the expansion unsatisfiable, to avoid further unnecessary matchings
                    for p in self.predicates[predicateIdx].expandTo:
                        if type(p) == ExpansionPredicate and p.evaluate() is False:
                            self.undo_substitution()
                            return False
        return True

    def substitute(self, replacingSym, replacedSym):
        """Substitute the symbol replacingSym with the symbol replacedSym in the clause."""
        if (replacingSym.id == replacedSym.id):
            print(f'The replacing symbol {replacingSym.show()} is the same as the replaced symbol {replacedSym.show()}.')
            return
        for predicate in (self.predicates + self.functions):
            predicate.substitutionTag = self.substitutionTag
            predicate.substitute(replacingSym, replacedSym)

    def undo_substitution(self, tag = None):
        """Undo all the substitutions with a substitution tag greater than a given tag or equal to current substitution tag."""
        if self.substitutionTag == 0:
            return
        if tag:
            #assert (tag > 0) and (tag < self.substitutionTag)
            if tag >= self.substitutionTag: 
                return
            else:
                self.substitutionTag = tag
        else:
            self.substitutionTag -= 1
        for predicate in (self.predicates + self.functions):
            predicate.undo_substitution(tag = self.substitutionTag)

    def ground(self):
        """Ground instantiation."""
        self.substitutionTag += 1
        for p in (self.predicates + self.functions):
            for a in p.arguments:
                # fix me, think about what to do with arithmetics when grounding a clause
                if isinstance(a, FunctionSymbol): continue
                if not a.isConstant:
                    gndCnst = GroundSymbol(a)
                    self.substitute(gndCnst, a)
        return self

    def undo_ground(self):
        for p in self.predicates:
            for a in p.arguments:
                if isinstance(a, GroundSymbol):
                    self.substitute(a.groundedFrom, a)
        return self

    def expansion(self):
        """
        For every occurrence of constant or recurrence of variable in extensional relation (non-builtin predicate), replace the constant/variable with a new variable, and add an equality to the clause using the contant/variable and the new variable.
        """
        firstAppearance = []
        predicates = [p for p in self.predicates if type(p) == Predicate]
        for p in predicates:
            for idx, a in enumerate(p.arguments):
                exSym = None
                if type(a) == Constant:
                    exSym = ConstantExpansion(a)
                elif type(a) == Variable:
                    if (a.id in firstAppearance):
                        exSym = VariableExpansion(a)
                    else:
                        firstAppearance.append(a.id)
                if exSym:
                    p.replace(exSym, idx)
                    exPredicate = ExpansionPredicate(exSym, a, p)
                    self.add_predicate(exPredicate)
                    p.expandTo.append(exPredicate)
        return self

    def undo_expansion(self):
        """Reverse expansion step."""
        # remove expansion predicates that have their source predicates remained in the clause
        exPredicates = [p for p in self.predicates if type(p) == ExpansionPredicate]
        loop = True
        while loop:
            loop = False
            for exPredicate in exPredicates:
                    targetPredicate = exPredicate.expandFrom
                    if isinstance(exPredicate.lhs, ExpansionSymbol):
                        # Since the every expansion variable is unique, if an expansion Predicate no longer contains a expansion symbol, it means the predicate from which the variable is expanded has matched with certain predicate and the expansion symbol has been substituted.
                        self.substitute(exPredicate.rhs, exPredicate.lhs)
                        self.predicates.remove(exPredicate)
                        loop = True
                    else:
                        # the predicate from which the variable is expanded is gone
                        # it is still possible that we need to remove the expansion equality predicate, when one side is a constant while the other side is a variable that appears in other non-extensional predicates
                        replacingSym = None
                        replacedSym = None
                        if (type(exPredicate.lhs) == Constant) and (type(exPredicate.rhs) in [Variable, GroundSymbol]): # ground symbol is instantiated from a variable
                            replacingSym = exPredicate.lhs
                            replacedSym = exPredicate.rhs
                        elif (type(exPredicate.rhs) == Constant) and (type(exPredicate.lhs) == GroundSymbol):
                            replacingSym = exPredicate.rhs
                            replacedSym = exPredicate.lhs
                        if replacedSym:
                            for p in self.predicates:
                                if (type(p) != ExpansionPredicate) and (replacedSym.id in p.argIdx):
                                    self.substitute(replacingSym, replacedSym)
                                    self.predicates.remove(exPredicate)
                                    loop = True
                                    break

        # also remove comparison predicates that evaluated to True
        compPred = [p for p in self.predicates if isinstance(p, ComparisonPredicate)]
        for p in compPred:
            if p.evaluate() is True:
                self.predicates.remove(p)

        # also remove repeated comparison predicates
        repPred = []
        compPred = [p for p in self.predicates if isinstance(p, ComparisonPredicate)]
        for i, pi in enumerate(compPred[1:], 1):
            for pj in compPred[0: i]:
                if ((pi.arguments[0].id == pj.arguments[0].id) and (pi.arguments[1].id == pj.arguments[1].id)):
                    repPred.append(pi)
                    break
                elif (isinstance(pi, Equal) and isinstance(pj, Equal)) and ((pi.arguments[0].id == pj.arguments[1].id) and (pi.arguments[1].id == pj.arguments[0].id)):
                    repPred.append(pi)
                    break
        for p in repPred:
            self.predicates.remove(p)

        for i,p in enumerate(self.predicates):
            if isinstance(p, ExpansionPredicate):
                self.predicates[i] = Equal(p.lhs, p.rhs)
            p.expandTo = []

        return self

    def partial_subsume(self, subsumedClause):
        self.z3Time = 0
        self.z3InvokedTimes = 0
        self.searchTime = 0
        self.totalRunTime = 0
        searchStart = timer()
        ret = []
        # ground instantiation
        subsumedClause.ground()

        subsumedExRelations = PredicateSet([p for p in subsumedClause.body if type(p) == Predicate])
        subsumedExRelationId = set([p.id for p in subsumedExRelations])
        subsumedEvaluables = PredicateSet([p for p in subsumedClause.body if type(p) != Predicate])
        allSubsumingExRelationIdx = [i for i in range(len(self.body)) if type(self.body[i]) == Predicate]
        size = len(self.body)
        potentialMatch = []
        matchShifter = [0]*len(allSubsumingExRelationIdx) #records current matched predicate for each predicate
        for i in range(len(allSubsumingExRelationIdx)):
            potentialMatch.append([p for p in subsumedExRelations if p.id == self.body[i].id])

        # subsuming clause expansion
        self.expansion()

        successSubclause = []
        for l in range(size, 0, -1):
            for matchingIdx in combinations(range(size), l):
                #print(f'{self.copy().undo_expansion().show()}')
                # redundant subclause check, if a subclause already subsumes the subsumed clause, we do not check the subset of  the subclause.
                redundantSubclause = False
                for s in successSubclause:
                    if set(matchingIdx) <= set(s):
                        redundantSubclause = True
                        break
                if redundantSubclause:
                    continue

                # if not all subsuming extensional relations are in the body of the subsumed clause, do not bother to test.
                if not (set([self.body[i].id for i in matchingIdx if type(self.body[i]) == Predicate]) <= subsumedExRelationId):
                    continue

                subsumingExRelationIdx = [i for i in matchingIdx if type(self.body[i]) == Predicate]
                subsumingExRelations = [self.body[i] for i in subsumingExRelationIdx]
                subsumingEvaluables = [self.body[i] for i in matchingIdx if type(self.body[i]) != Predicate]

                # Subsuming evaluables should also include the expansion part
                for p in subsumingExRelations:
                    subsumingEvaluables += p.expandTo
                subsumingEvaluables = PredicateSet(subsumingEvaluables)
                #print(f"subsumingExRelations: {Rule(body = subsumingExRelations).show()}")
                #print(f"subsumingEvaluables: {subsumingEvaluables.show()}\n")
                N = len(subsumingExRelationIdx)
                #print(f'subsuming extensional relations: {PredicateSet(subsumingExRelations).show()}')
                #print(f'subsuming evaluables: {subsumingEvaluables.show()}\n')
                if N == 0: continue
                predItr = 0
                predIdx = subsumingExRelationIdx[predItr]
                while predItr < N and predItr >= 0:
                    # match subsumingExRelations[predItr]
                    matchedPredicate = potentialMatch[predIdx][matchShifter[predIdx]]
                    match = self.match_predicate(predIdx, matchedPredicate)
                    if match:
                        if (predItr == N - 1):  # all predicates matched, check comparion formulas
                            unsat = True
                            if (len(subsumingEvaluables) > 0):
                                z3Start = timer()
                                unsat = not check_sat([subsumingEvaluables.copy().negate(), subsumedEvaluables])
                                z3End = timer()
                                self.z3InvokedTimes += 1
                                self.z3Time += (z3End - z3Start)
                            if unsat:
                                residueRelations = [p for i,p in enumerate(self.body) if i not in subsumingExRelationIdx and p not in subsumingEvaluables]
                                residueEvaluables = PredicateSet([p for p in residueRelations if type(p) != Predicate])
                                # check if residue is redundant
                                sat = True
                                if (len(residueEvaluables) > 0):
                                    z3Start = timer()
                                    sat = check_sat([residueEvaluables, subsumedEvaluables])
                                    z3End = timer()
                                    self.z3InvokedTimes += 1
                                    self.z3Time += (z3End - z3Start)
                                if sat:
                                    residue = Rule(body = residueRelations).copy().undo_expansion().undo_ground()
                                    ret.append(residue)
                                    successSubclause.append(matchingIdx)
                            else:
                                # In this case, we have matched all the extensional relations in the subsuming subclause, but the evaluable relations do not agree, we then leave the evaluable relations as residue if they don't make a redundant residue.
                                residueRelations = [p for i,p in enumerate(self.body) if i not in subsumingExRelationIdx]
                                residueEvaluables = PredicateSet([p for p in residueRelations if type(p) != Predicate])
                                # check if residue is redundant
                                sat = True
                                if (len(residueEvaluables) > 0):
                                    z3Start = timer()
                                    sat = check_sat([residueEvaluables, subsumedEvaluables])
                                    z3End = timer()
                                    self.z3InvokedTimes += 1
                                    self.z3Time += (z3End - z3Start)
                                if sat:
                                    residue = Rule(body = residueRelations).copy().undo_expansion().undo_ground()
                                    ret.append(residue)
                                    successSubclause.append(matchingIdx)

                            self.undo_substitution()
                        else:
                            predItr += 1
                            predIdx = subsumingExRelationIdx[predItr]
                            continue

                    while predItr >= 0:
                        if matchShifter[predIdx]+1 == len(potentialMatch[predIdx]):
                            # if there is not more candidate for current predicate to match, we release the matching of the previous predicate, and try to match the previous predicate to the next candidate
                            self.undo_substitution()
                            matchShifter[predIdx] = 0
                            predItr -= 1
                            predIdx = subsumingExRelationIdx[predItr]
                        else:
                            matchShifter[predIdx] += 1
                            break
        self.undo_ground().undo_expansion()
        subsumedClause.undo_ground()
        searchEnd = timer()
        self.totalRunTime = (searchEnd - searchStart)
        self.searchTime = self.totalRunTime - self.z3Time
        if len(ret) == 0:
            return [self]
        else:
            return ret

    def sort_clause(self):
        self.predicates = sorted(self.predicates, key=lambda predicate:predicate.id)

    def copy(self):
        ret = Rule(head = self.head.copy(), body = [p.copy() for p in self.body])
        for nPred, oPred in zip(ret.body, self.body):
            for p in oPred.expandTo:
                if p not in self.body: continue # this is a function auxiliary predicate
                nExPred = ret.body[self.body.index(p)]
                nExPred.expandFrom = nPred
                nPred.expandTo.append(nExPred)
        return ret

    def negate(self):
        print('Negation on a Rule object is undefined!')

    def show(self):
        return f"{self.head.show()} :- {PredicateSet.show(self, conjunctConnector = ', ')}."

def check_sat(clauses):
    s = Solver()
    for c in clauses:
        predicates = []
        for p in c.predicates:
            if isinstance(p, Function): continue # the corresponding arithmetic symbol will extend itself to this arithmetic expression during evaluation
            if p.isNegated:
                predicates.append(Not(p.evaluate()))
            else:
                predicates.append(p.evaluate())
        if c.isConjunction:
            s.add(predicates)
        else:
            s.add(Or(predicates))
    return s.check() == sat