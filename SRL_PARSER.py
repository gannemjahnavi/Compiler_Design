import copy
import argparse

def revGAug(rules):
    nRule = []
    for rule in rules:
        k = rule.split("->")
        left = k[0].strip()
        right = k[1].strip().split('|')
        for right1 in right:
            right1 = right1.strip().split()
            right1.append('.')
            nRule.append([left, right1])
    return nRule

def everyRule(rules,startsymbol):
    
	nRule = []

	for rule in rules:
	
		k = rule.split("->")
		left = k[0].strip()
		right = k[1].strip()

		multiright = right.split('|')
		for right1 in multiright:
			right1 = right1.strip().split()
			nRule.append([left, right1])
	return nRule
    
def augG(rules):
    nstart = rules[0].split("->")[0].strip() + "'"
    nstartRule = nstart + " -> " + rules[0].split("->")[0].strip()
    augmented = [nstartRule] + rules
    return augmented

def findReverseClosure(inputstate, dotSymbol):
    global startsymbol, separatedRulesList, statesDict
    closureSet = []
    if dotSymbol == startsymbol:
        for rule in separatedRulesList:
            if rule[0] == dotSymbol:
                closureSet.append(rule)
    else:
        closureSet = inputstate
    prevLen = -1
    while prevLen != len(closureSet):
        prevLen = len(closureSet)
        tempClosureSet = []
        for rule in closureSet:
            indexOfDot = rule[1].index('.')
            if indexOfDot != 0:
                dotPointsHere = rule[1][indexOfDot - 1]
                for inrule in separatedRulesList:
                    if dotPointsHere == inrule[0] and inrule not in tempClosureSet:
                        tempClosureSet.append(inrule)
        for rule in tempClosureSet:
            if rule not in closureSet:
                closureSet.append(rule)
    return closureSet

def compute_GOTO(state):
    global statesDict, stateCount
    generateStatesFor = []
    for rule in statesDict[state]:
        if rule[1][0] != '.':
            indexOfDot = rule[1].index('.')
            dotPointsHere = rule[1][indexOfDot - 1]
            if dotPointsHere not in generateStatesFor:
                generateStatesFor.append(dotPointsHere)
    if len(generateStatesFor) != 0:
        for symbol in generateStatesFor:
            GOTO(state, symbol)

def GOTO(state, charPrevToDot):
    global statesDict, stateCount, stateofmap
    newState = []
    for rule in statesDict[state]:
        indexOfDot = rule[1].index('.')
        if indexOfDot != 0:
            if rule[1][indexOfDot - 1] == charPrevToDot:
                shiftedRule = copy.deepcopy(rule)
                shiftedRule[1][indexOfDot] = shiftedRule[1][indexOfDot - 1]
                shiftedRule[1][indexOfDot - 1] = '.'
                newState.append(shiftedRule)
    addClosureRules = []
    for rule in newState:
        indexDot = rule[1].index('.')
        if indexDot != 0:
            closureRes = findReverseClosure(newState, rule[1][indexDot - 1])
            for rule in closureRes:
                if rule not in addClosureRules and rule not in newState:
                    addClosureRules.append(rule)
    for rule in addClosureRules:
        newState.append(rule)
    stateExists = -1
    for state_num in statesDict:
        if statesDict[state_num] == newState:
            stateExists = state_num
            break
    if stateExists == -1:
        stateCount += 1
        statesDict[stateCount] = newState
        stateofmap[(state, charPrevToDot)] = stateCount
    else:
        stateofmap[(state, charPrevToDot)] = stateExists

    if stateExists == -1:
        print(f"GOTO(I{state}, {charPrevToDot}) = I{stateCount}")
    else:
        print(f"GOTO(I{state}, {charPrevToDot}) = I{stateExists}")


def last(rule):
    global rules, ntermuserdef, termuserdef, diction, lasts
    if not rule:
        return []
    
    lastsymbol = []
    if rule and rule[-1] in termuserdef:
        lastsymbol.append(rule[-1])
    elif rule and rule[-1] == '#':
        lastsymbol.append('#')
    else:
        nonteminal = rule[-1]
        if nonteminal in diction:
            rightrules = diction[nonteminal]
            for right in rightrules:
                if right == rule:
                    continue 
                lastofright = last(right)
                lastsymbol.extend(lastofright)
    
    return lastsymbol

def precede(nt):
    global startsymbol, rules, ntermuserdef, \
        termuserdef, diction, lasts, precedes
    res = None
    solset = set()
    if nt == startsymbol[0]:
       
        solset.add('$')
    elif nt == startsymbol:
        solset.add('$')
 
    
    for currentnonterminal in diction:
        right = diction[currentnonterminal]
         
        for subrule in right:
            if nt in subrule:
               
                while nt in subrule:
                    indexnonter = subrule.index(nt)
                    subrule = subrule[:indexnonter]
                     
                    if len(subrule) != 0:
                       
                        res = last(subrule)
                         
                        if '#' in res:
                            newList = []
                            res.remove('#')
                            ansNew = follow(currentnonterminal)
                            if ansNew != None:
                                if type(ansNew) is list:
                                    newList = res + ansNew
                                else:
                                    newList = res + [ansNew]
                            else:
                                newList = res
                            res = newList
                            
                    else:
                       
                        if nt != currentnonterminal:
                            res = precede(currentnonterminal)
 
                    if res is not None:
                        if type(res) is list:
                            for g in res:
                                solset.add(g)
                        else:
                            solset.add(res)
    return list(solset)

                
def createParseTable(statesDict, stateofmap, T, NT):
    global separatedRulesList, diction, originalrules,Table

    diction= {}
    rows = list(statesDict.keys())
    cols = T + ['$'] + NT

    Table = []
    tempRow = [] 
    for y in range(len(cols)):
        tempRow.append('')
    for x in range(len(rows)):
        Table.append(copy.deepcopy(tempRow))


    for entry in stateofmap:
        state = entry[0]
        symbol = entry[1]
        
        a = rows.index(state)
        b = cols.index(symbol)
        if symbol in NT:
            Table[a][b] = Table[a][b] + f"{stateofmap[entry]} "
        elif symbol in T:
            Table[a][b] = Table[a][b] + f"S{stateofmap[entry]} "

    numbered = {}
    keycount = 0
    for rule in separatedRulesList:
        tempRule = copy.deepcopy(rule)
        tempRule[1].remove('.')
        numbered[keycount] = tempRule
        keycount += 1

    addedR = f"{separatedRulesList[0][0]} -> " f"{separatedRulesList[0][1][1]}"
    originalrules.insert(0, addedR)

    for rule in originalrules:
        k = rule.split("->")
        k[0] = k[0].strip()
        k[1] = k[1].strip()
        right = k[1]
        multiright = right.split('|')
        for i in range(len(multiright)):
            multiright[i] = multiright[i].strip()
            multiright[i] = multiright[i].split()
        diction[k[0]] = multiright
    for stateno in statesDict:
        for rule in statesDict[stateno]:
            if rule[1][0] == '.':
                temp2 = copy.deepcopy(rule)
                temp2[1].remove('.')
                for key in numbered:
                    if numbered[key] == temp2:
                        precederes = precede(rule[0])

                        for col in precederes:
                            index = cols.index(col)
                            if key == 0:
                                Table[stateno][index] = "Accept"
                            else:
                                Table[stateno][index] = Table[stateno][index] + f"R{key} "
    

    print("\nSRL(1) parsing table:\n")
    frmt = "{:>8}" * len(cols)
    print("  ", frmt.format(*cols), "\n")
    ptr = 0
    j = 0
    for y in Table:
        frmt1 = "{:>8}" * len(y)
        print(f"{j:>3} {frmt1.format(*y)}".format('I' + str(j)))
        j += 1

def printStates():
    for state_num, items in statesDict.items():
        print(f"I{state_num}:")
        for item in items:
            print("   ", item[0], "->", ' '.join(item[1]))
        print()

def parseinputstr(inputstr, grules, parsing_table):

    stack = [0]
    inputtok = ['$'] + ['num' if token.isdigit() else token for token in inputstr.split()]
    
    inputidx = len(inputtok)-1
    
    while 0 < len(inputtok):
        currstate = stack[-1]
        curttok = inputtok[inputidx]

       
        if gcolindex(curttok) is None :
            return False
        action = parsing_table[currstate][gcolindex(curttok)]

        if action == "Accept":
            return True  

        if action == "":
            return False 

        if action[0] == 'S':
            stack.append(curttok)
            stack.append(int(action[1:]))
            inputidx -= 1
        elif action[0] == 'R':
            rule_num = int(action[1:])

            left, right = grules[rule_num - 1]
            for _ in right:
                stack.pop()
                stack.pop()
            currstate = stack[-1]
            stack.append(left)
            stack.append(int(parsing_table[currstate][gcolindex(left)]))
        else:
            return False

def gcolindex(token):
    columns = termuserdef + ['$'] + ntermuserdef
    column_mapping = {token: i for i, token in enumerate(columns, start=0)}
    return column_mapping.get(token)
    


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="SRL(1) Parser")
    parser.add_argument("input_file", type=str, help="File containing the input string")
    args = parser.parse_args()

    originalrules = []
    with open(args.input_file, "r") as file:
        for line in file:
            originalrules.append(line.strip())  


    print("Original rules: ",originalrules)            

    
    sample_rules = augG(originalrules)
    augmented_rules = revGAug(sample_rules)
    separatedRulesList = augmented_rules
    
    startsymbol = str(input("Enter start symbol: "))
    allrules=everyRule(originalrules,startsymbol)

    ntermuserdef = list(set([item[0] for item in allrules if item[0].isupper()]))
    termuserdef = list(set([sub_item for item in allrules for sub_item in item[1] if not sub_item.isupper()]))

    
    statesDict = {}
    stateCount = 0
    stateofmap = {}

    ss1= startsymbol+"'"
    initialstate = [[ss1, [startsymbol, "."]]]
    
    startsymbol = startsymbol + "'"
    dotSymbol = startsymbol
    closure = findReverseClosure(initialstate, dotSymbol)
    statesDict[stateCount] = closure

    print("\nClosure:")
    for rule in closure:
        print(rule[0], '->', ' '.join(rule[1]))

    print("\n")
    print("GOTO Statements")
    i = 0
    while i <= stateCount:
        compute_GOTO(i)
        i += 1

    createParseTable(statesDict, stateofmap, termuserdef, ntermuserdef)
    
    
        
    print("\n")
    print("STATES GENERATED")
    printStates()

    inp = str(input("Enter input string(with spaces in between): "))

    
    if parseinputstr(inp, allrules, Table):
        print("Accepted!")
    else:
        print("Rejected!")
    
