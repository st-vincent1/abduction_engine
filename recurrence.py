import logic as lo
import aodag as dag
import itertools
import pprint as pp
import copy
from operator import itemgetter

"""
Satisfied if all consequents in rule are among nodes
"""
def satisfied(rule, nodes):
    nodesArgs = [node.arg for node in nodes]
    sat = True
    for n in rule.conse:
        if n not in nodesArgs:
            sat = False
    return sat

"""
Pattern matching
"""
def backchain(rollingNodes, rule):
    usedNodes = []
    bP = []
    if satisfied(rule, rollingNodes):
        usedNodes += [node for node in rollingNodes if node.arg in rule.conse]
        bP += rule.ante
    return (bP, usedNodes)

def indexUpdate(index, rollingNodes):
    for o in rollingNodes:
        if lo.predPattern(o.arg) not in index.keys():
            index[lo.predPattern(o.arg)] = [o]
        else:
            index[lo.predPattern(o.arg)].append(o)
    return index
"""
Main function;
Continually apply backchaining and unification until convergence/reached max depth
Update the graph as you go along
"""
def backchainAndUnify(KB, rollingNodes, G, Litd, index, obsvNodes, d=3):
    Refd = dict()
    Axd = dict()
    Numd = dict()
    uniPair = dict()
    uniPredicate = dict()
    seriesNodes = copy.deepcopy(rollingNodes)

    # Ghost unification

    while(d>0):
        # Backchaining
        for axiom in KB:
            if axiom.no not in Axd.keys():
                Axd[axiom.no] = dag.Node(axiom.no, 'ax')
                Numd[axiom.no] = dag.Node(axiom.no, 'num')
                dag.addChildren(G, Numd[axiom.no], [Axd[axiom.no]])
            # Axiom is of the form HornClause(args, args)
            # rollingNodes is the list of Nodes already explored
            # bP is a list of backchained PREDICATES
            # Need to: create nodes for predicates, THEN connect bp-axiom-up
            (bP, usedNodes) = backchain(rollingNodes, axiom) #Parse root?
            if bP:
                #Something was bchained -> create axiom node
                dag.addChildren(G, Axd[axiom.no], usedNodes)
                for b in bP:
                    if b not in Litd.keys():
                        Litd[b] = dag.Node(b, 'lit')
                    pp = lo.predPattern(b)
                    index[pp] = [Litd[b]] if pp not in index.keys() else index[pp] + [Litd[b]]
                    dag.addChildren(G, Litd[b], [Axd[axiom.no]])
                    seriesNodes.append(Litd[b])

            #Putting Refs in the graph
            for a in axiom.conse:
                if a not in Refd.keys():
                    if a in Litd.keys():
                        Refd[a] = dag.Node(a, 'ref', False, True if Litd[a] in obsvNodes else False)
                if a in Refd.keys():
                    dag.addChildren(G, Refd[a], [Axd[axiom.no]])
        rollingNodes.extend(seriesNodes)
        rollingNodes = list(dict.fromkeys(rollingNodes))

        # Unification
        for x in seriesNodes:
            # For each backchained literal, try to unify it with whatever you can
            xPttn = lo.predPattern(x.arg) # can only unify literals of same pattern
            if xPttn in index.keys(): # if not in index then there's nothing to unify
                for y in index[xPttn]: # try to unify against every literal in index
                    # Now I'm at the pair. want to know if these are unifiable [also no if theta empty]
                    theta = lo.unifyTerms(x.arg,y.arg)
                    if not theta:
                        break # to avoid (x=y,y=x)
                    for pair in theta.items():
                        if pair not in uniPair.keys(): # if no x=y node in graph
                            uniPair[pair] = dag.Node(pair, 'eq') #create node
                        if xPttn not in uniPredicate.keys():
                            uniPredicate[xPttn] = dag.Node(xPttn, 'uni')
                            dag.addChildren(G, uniPredicate[xPttn], [x,y])
                            if not x.obsv:
                                dag.addChildren(G, uniPredicate[xPttn], [Numd[G[x][0].arg]])
                            if not y.obsv:
                                dag.addChildren(G, uniPredicate[xPttn], [Numd[G[y][0].arg]])
                        if uniPair[pair] not in G.keys() or G[uniPair[pair]] != uniPredicate[xPttn]: # if the child of unif
                            dag.addChildren(G, uniPair[pair], [uniPredicate[xPttn]])
        seriesNodes = []
        d -= 1
    return Refd, Axd, Numd, uniPair, uniPredicate

"""
Input parser
Takes input from observations' and rules' boxes and parses them
into observations and KB rules
"""
def parseInput(obsvNodes, f):
    KB = []
    index = dict()
    rollingNodes = []
    G = dict()
    Litd = dict()
    obsvNodes = [x.split('(') for x in obsvNodes]
    # convert obsv to Nodes

    for i in obsvNodes:
        a = parseLit(i)
        aNode = dag.Node(a, 'lit', True)
        Litd[a] = aNode
        rollingNodes.append(aNode)

    obsvNodes = copy.deepcopy(rollingNodes)
    G = dag.initGraph(rollingNodes)
    # index stores lists of nodes that satisfy a certain predicate pattern
    index = indexUpdate(index, rollingNodes)

    for line in f:
        implication = line.strip().split(' -- ')
        antecedents = implication[0].split(' and ')
        consequents = implication[1].split(' and ')
        antecedentsArgs, consequentsArgs = parse(antecedents), parse(consequents)
        KB.append(lo.Rule(len(KB)+1, antecedentsArgs, consequentsArgs))
    return KB, Litd, rollingNodes, G, index, obsvNodes

def parseLit(i):
    symbol = i[0]
    args = i[1][:-1].split(',')
    args = [arg.strip() for arg in args]
    return lo.Form(symbol, args)

def parse(varList):
    varList = [varList[i].split('(') for i in range(len(varList))]
    varList = [parseLit(i) for i in varList]
    return varList


def topSort(G):
    # Degree is a list of topologically sorted nodes
    order = []
    vis = dict()
    degree = dict()
    for i in G.keys():
        vis[i] = False if i.family not in ['num', 'ref'] else True
        degree[i] = 0
    for i in G:
        if not vis[i]:
            vis[i] = True
            degree = dag.dfsDegree(G, i, degree, vis)
    #Topsort
    for i in G.keys():
        vis[i] = False if i.family not in ['num', 'ref'] else True
    for i in degree.keys():
        if degree[i] == 0 and not vis[i]:
            vis[i] = True
            dag.dfsTop(G, i, order, degree, vis)
    return order

"""
Compute parents for nodes and compile into a list
"""
def computePar(order, G):
    par = [x[:] for x in [[]]*(len(order))]
    children = [x[:] for x in [[]]*(len(order))]
    orderIndex = dict()
    for i in range(len(order)):
        orderIndex[order[i]] = i

    # Compute par
    for node in order:
        for child in G[node]:
            if child.family not in ['ref', 'num']:
                par[orderIndex[child]].append(orderIndex[node])
                children[orderIndex[node]].append(orderIndex[child])
    return par, children, orderIndex

"""
Compute all possible combinations for T/F value assignments in graph
"""
def computeCombo(order, par, children, orderIndex, G):
    combo = [[]]
    for i in order:
        combo = dag.traversal(G, i, combo, par, orderIndex)
    # Delete useless combinations (those which have false observables)
    obsvNodes = [orderIndex[i] for i in order if i.obsv == True]
    combo = dag.checkObsv(combo, obsvNodes)
    combo = dag.usefulCombo(combo, children)
    return combo

"""
Compute all valid hypotheses
"""
def computeHyp(combo, order, orderIndex, par, Refd, G):
    score = [0]*len(combo)
    hyp = [x[:] for x in [[]]*(len(combo))]
    for j in range(len(combo)):
        c = combo[j]
        refParents = [G[x] for x in Refd.values()]
        refParents = list(set([item for sublist in refParents for item in sublist]))
        trueParents = [x for x in order if x.family == 'ax' and c[orderIndex[x]]]
        refCount = len(list(set(refParents) & set(trueParents)))
        uniCount = len([x for x in order if x.family == 'uni' and c[orderIndex[x]]])
        score[j] = refCount + uniCount

        for i in range(len(combo[j])):
            if combo[j][i] == True:
                noTrueParents = False
                for p in par[i]:
                    if combo[j][p] == True and order[p].family != 'uni':
                        noTrueParents = True
                        break
                if noTrueParents == False:
                    hyp[j].append(order[i])
    x = sorted(list(zip(score, range(len(score)))), reverse = True)
    print(x)
    hyps = [hyp[j] for i,j in x]
    print(hyps)
    return hyp

"""
Print functions
invoked to form strings containing data from algorithm proceedings/output and put in boxes in the application
"""
def printHyp(hyp):
    strg = ""
    for i in range(1, len(hyp)+1):
        mph = "" if i>1 else "(most probable hypothesis)"
        strg = strg + f'Hypothesis #{i} {mph}:\n'
        # for node in hyp[i-1]:
        #     print(node)
            # if node.family == 'eq':
            #     strr = str(node.arg[0]) + u'\21a6' + str(node.arg[1])
            #     print(strr)
        args = [' == '.join(node.arg) if node.family == 'eq' else str(node.arg) for node in hyp[i-1]]
        strg = strg + u' \u2227 '.join(args) + "\n"
    return strg

def printGraph(G):
    strg = "\nGraph:\n"
    for x in G.keys():
        strg = strg + str(x) + " --> " + str(G[x])
        strg += "\n"
    strg += "Note that <num> and <eq> nodes serve no purpose in establishing hypotheses; they're there for other uses of the system. Thus they're not accounted for from now on."
    return strg

def printKB(KB):
    strg = "Knowledge Base:\n"
    for i in range(1, len(KB)+1):
        strg = strg + str(KB[i-1]) + "\n"
    return strg

def printOrder(orderIndex):
    strg = "\n\nTopological order of nodes:\n"
    for i in orderIndex.keys():
        strg = strg + f'{str(orderIndex[i]+1)}: {repr(i)}\n'
    return strg

"""
Function that can be ran independently of the app to work with it in commandline
Running python recurrence.py will invoke this
"""
def abduce(input=None, d=3):
    d = 5
    f = open("test1a", "r")
    KB, Litd, rollingNodes, G, index, obsvNodes = parseInput(f)
    """
    Assumption: KB is filtered so that each rule is going to be useful for backchaining.
    Not necessary, though speeds up inference. Will do if time allows, it can be done with just input.
    """
    # This goes in the work in progress field
    printKB(KB)

    Refd, Axd, Numd, uniPair, uniPredicate = backchainAndUnify(KB, rollingNodes, G, Litd, index, obsvNodes, d)

    # Work in progress field
    printGraph(G)
    # Calculate topological order for nodes
    order = topSort(G)

    """
    Now on to creating hypotheses
    each node is given a number depending on its order from topsort
    order is the topological order of nodes
    orderIndex is a dictionary node : number
    par is a reverse order graph computed on those numbers
    combo is a list of all possible combinations of truth/false assignments to nodes in graph
    """
    # Compute par, children and orderIndex
    par, children, orderIndex = computePar(order, G)
    # Compute combo
    combo = computeCombo(order, par, children, orderIndex, G)
    # Create a list of hypotheses
    hyp = computeHyp(combo, order, par)
    # Print out all hypotheses
    printHyp(hyp)

    ###TODO

    #update ref and num
    # Update NumbU
    # From now on work on G.. or incorporate num and ref into the previous representation
    return

if __name__ == '__main__':
    abduce()
