newPackage(
    "SkewTableaux",
    Version => "0.3",
    Date => "July 18, 2025",
    Authors => {
	{Name => "John Graf", Email => "grafjohnr@gmail.com", HomePage => "https://j-graf.github.io/"}},
    Headline => "a package for constructing skew tableaux",
    Keywords => {"Combinatorics"},
    DebuggingMode => false,
    PackageImports => {"Permutations"}
    )

export {"SkewTableau", "skewTableau",
        "shape", "shape0", "rowEntries", "colEntries", "colRange", "isSkew", "isYoungTableau",
        "indexToPosition", "positionToIndex", "alignToZero", "verticalConcatenate", "shift", "unshift",
        "allSSYT", "JTshapes", "JTtableaux"}

SkewTableau = new Type of HashTable
skewTableau = method(TypicalValue => SkewTableau)
skewTableau (Partition,Partition,List) := (lam,mu,theList)->(
    maxLength := max {#lam,#mu};
    lamPadded := new Partition from (toList(lam)|toList((maxLength-#lam):0));
    muPadded := new Partition from (toList(mu)|toList((maxLength-#mu):0));

    numBoxesNeeded := sum for i from 0 to #lamPadded-1 list max(lamPadded#i-muPadded#i,muPadded#i-lamPadded#i);
    
    if (numBoxesNeeded != #theList) then error "partition sizes do not match with the length of the list";
    if any(theList, theElt -> theElt === null) then error "filling must not contain null entries";

    new SkewTableau from {
        "outerShape" => lam,
        "innerShape" => mu,
        values => theList
        }
    )
skewTableau (Partition,List) := (lam,theList)->(
    skewTableau(lam,new Partition from {},theList)
    )
skewTableau (Partition,Partition) := (lam,mu) -> (
    (lam',mu') := shape0(lam,mu);
    numBoxesNeeded := sum for i from 0 to #lam'-1 list max(lam'#i-mu'#i,mu'#i-lam'#i);
    
    skewTableau(lam,mu,toList(numBoxesNeeded:""))
    )
skewTableau Partition := lam -> (
    numBoxesNeeded := sum for i from 0 to #lam-1 list max(lam#i,-lam#i);
    
    skewTableau(lam,new Partition from {},toList (numBoxesNeeded:""))
    )

shape = method(TypicalValue => Sequence)
shape (Partition,Partition) := (lam,mu) -> (
    lamNumTrailingZeros := # for i from 1 to #lam list (if lam#-i == 0 then 1 else break);
    muNumTrailingZeros := # for i from 1 to #mu list (if mu#-i == 0 then 1 else break);

    lamShortened := (toList lam)_(toList(0..(#lam-1-lamNumTrailingZeros)));
    muShortened := (toList mu)_(toList(0..(#mu-1-muNumTrailingZeros)));

    (new Partition from lamShortened, new Partition from muShortened)
    )
shape SkewTableau := T -> (
    shape(T#"outerShape", T#"innerShape")
    )

shape0 = method(TypicalValue => Sequence)
shape0 (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = shape(lam,mu);
    maxLength := max(#lam,#mu);

    lamPadded := toList(lam)|toList((maxLength - #lam):0);
    muPadded := toList(mu)|toList((maxLength - #mu):0);
    
    (new Partition from lamPadded, new Partition from muPadded)
    )
shape0 SkewTableau := T -> (
    shape0 shape T
    )

-*
shapeReduced = method(TypicalValue => Sequence)
shapeReduced (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = shape0(lam,mu);
    minMu := min toList mu;
    
    lamReduced := for thePart in lam list thePart - minMu;
    muReduced := for thePart in mu list thePart - minMu;
    
    (new Partition from lamReduced, new Partition from muReduced)
    )
shapeReduced SkewTableau := T -> (
    shapeReduced shape0 T
    )
*-

alignToZero = method(TypicalValue => SkewTableau)
alignToZero (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = shape0(lam,mu);
    minPart := min(toList mu | toList lam);

    lamAligned := for thePart in lam list thePart - minPart;
    muAligned := for thePart in mu list thePart - minPart;

    (new Partition from lamAligned, new Partition from muAligned)
    )
alignToZero SkewTableau := T -> (
    (lamAligned,muAligned) := alignToZero shape0 T;
    skewTableau(lamAligned, muAligned, entries T)
    )

SkewTableau == SkewTableau := (T1,T2) -> (
    (lam1,mu1) := shape0 T1;
    (lam2,mu2) := shape0 T2;

    entries T1 == entries T2 and toList lam1 == toList lam2 and toList mu1 == toList mu2
    )

hasNegativeRow = method(TypicalValue => Boolean)
hasNegativeRow SkewTableau := T -> (
    (lam,mu) := shape0 T;
    
    any(0..(#lam-1), i -> mu#i > lam#i)
    )

normalizeNegativeRows = method(TypicalValue => SkewTableau)
normalizeNegativeRows SkewTableau := T -> (
    if not hasNegativeRow T then return T;
    
    (lam,mu) := shape0 T;

    lam' := new Partition from for i from 0 to #lam-1 list max(lam#i,mu#i);
    mu' := new Partition from for i from 0 to #lam-1 list min(lam#i,mu#i);
    
    skewTableau(lam',mu',entries T)
    )

listNegativeRows = method(TypicalValue => List)
listNegativeRows SkewTableau := T -> (
    (lam,mu) := shape0 T;

    for i from 0 to #lam-1 list (mu#i > lam#i)
    )

SkewTableau^ZZ := (T,rowIndex) -> (
    (lam,mu) := shape0 normalizeNegativeRows T;
    colInds := colRange T;

    if rowIndex < 0 then (
        rowIndex = #lam + rowIndex;
        );
    if rowIndex >= #lam or rowIndex < 0 then error "index out of bounds";
    
    numBoxesAbove := sum for i from 0 to rowIndex-1 list (lam#i-mu#i);
    emptyBoxesLeft := toList((mu#rowIndex - colInds#0):null);
    filledBoxes := for i from numBoxesAbove to numBoxesAbove+lam#rowIndex-mu#rowIndex-1 list T#values#i;
    emptyBoxesRight := toList((colInds#-1 - lam#rowIndex + 1):null);
    
    emptyBoxesLeft|filledBoxes|emptyBoxesRight
    )

SkewTableau_ZZ := (T,colIndex) -> (
    (lam,mu) := shape0 normalizeNegativeRows T;
    colInds := colRange T;

    if colIndex < colInds#0 or colIndex > colInds#-1 then error "index out of bounds";

    for rowIndex from 0 to #lam-1 list (
        if colIndex < mu#rowIndex or colIndex >= lam#rowIndex then (
            null
            ) else (
            T^rowIndex#(colIndex-colInds#0)
            )
        )
    )

SkewTableau_Sequence := (T,thePosition)->(
    (rowIndex,colIndex) := thePosition;
    colInds := colRange T;
    
    ans := T^rowIndex#(colIndex-colInds#0);
    if ans === null then error "index out of range";
    ans
    )

rowEntries = method(TypicalValue => List)
rowEntries (ZZ,SkewTableau) := (rowIndex,T) -> delete(null,T^rowIndex)

colEntries = method(TypicalValue => List)
colEntries (ZZ,SkewTableau) := (colIndex,T) -> delete(null,T_colIndex)

net SkewTableau := T -> (
    (lam,mu) := shape0 normalizeNegativeRows T;

    if #lam == 0 then return "∅";

    isNegativeRow := listNegativeRows T;

    --innerShapeString := if DrawInnerShape then "■" else " ";
    innerShapeString := "■";

    (muSmallest, lamLargest) := (min(min toList mu,0), max(max toList lam,0));
    colWidth := if #entries T == 0 then 1 else max for theBox in entries T list #toString(theBox);
    colWidth = max {colWidth + 2,3};
    hasNegativeParts := any(toList(lam)|toList(mu), thePart -> thePart < 0);
    
    boxColumns := for colIndex from muSmallest to lamLargest-1 list (
        currCol := if colIndex >= mu#0 and colIndex < lam#0 then concatenate(colWidth:"─") else concatenate(colWidth:" ");
        for rowIndex from 0 to #lam-1 do (
            isBox := colIndex >= mu#rowIndex and colIndex < lam#rowIndex;
            isBoxBelow := rowIndex < #lam-1 and colIndex >= mu#(rowIndex+1) and colIndex < lam#(rowIndex+1);

            boxString := if isBox then (
                boxPadding := if isNegativeRow#rowIndex then "░" else " ";
                boxEntry := toString((rowEntries(rowIndex,T))#(colIndex-mu#rowIndex));
                if isNegativeRow#rowIndex and #boxEntry == 0 then boxEntry = "░";
                boxPadding|boxEntry|boxPadding
                ) else if (colIndex < 0 and colIndex >= lam#rowIndex) or (colIndex >= 0 and colIndex < mu#rowIndex) then (
                " "|concatenate((colWidth-2):innerShapeString)|" "
                ) else (
                " "
                );

            belowString := if isBox or isBoxBelow then "─" else " ";
            belowString = concatenate(colWidth:belowString);
            
            currCol = currCol||boxString||belowString;
            );
        currCol
        );

    cornerChar := (leftUp,rightUp,leftDown,rightDown) -> (
        cornerHash := new HashTable from {
            "0000" => " ",
            "0001" => "┌",
            "0010" => "┐",
            "0011" => "┬",
            "0100" => "└",
            "0101" => "├",
            "0110" => "┼",
            "0111" => "┼",
            "1000" => "┘",
            "1001" => "┼",
            "1010" => "┤",
            "1011" => "┼",
            "1100" => "┴",
            "1101" => "┼",
            "1110" => "┼",
            "1111" => "┼"
            };

        theKey := concatenate({leftUp,rightUp,leftDown,rightDown} / (i -> if i then toString(1) else toString(0)));
        
        cornerHash#theKey
        );

    sepColumns := for colIndex from muSmallest to lamLargest list (
        isBoxLeftUp := false;
        isBoxRightUp := false;
        isBoxRightDown := colIndex >= mu#0 and colIndex < lam#0;
        isBoxLeftDown := colIndex-1 >= mu#0 and colIndex-1 < lam#0;
        
        currColNet := if colIndex == 0 and hasNegativeParts then (
                "║"
                ) else (
                cornerChar(isBoxLeftUp,isBoxRightUp,isBoxLeftDown,isBoxRightDown)
                );
        
        for rowIndex from 0 to #lam-1 do (

            isBoxLeft := colIndex-1 >= mu#rowIndex and colIndex-1 < lam#rowIndex;
            isBoxRight := colIndex >= mu#rowIndex and colIndex < lam#rowIndex;

            isBoxLeftUp = isBoxLeft;
            isBoxRightUp = isBoxRight;
            isBoxRightDown = rowIndex < #lam-1 and colIndex >= mu#(rowIndex+1) and colIndex < lam#(rowIndex+1);
            isBoxLeftDown = rowIndex < #lam-1 and colIndex-1 >= mu#(rowIndex+1) and colIndex-1 < lam#(rowIndex+1);

            boxString := if colIndex == 0 and hasNegativeParts then (
                "║"
                ) else if isBoxRight or isBoxLeft then (
                "│"
                ) else (
                " "
                );

            belowString := if colIndex == 0 and hasNegativeParts then (
                "║"
                ) else (
                cornerChar(isBoxLeftUp,isBoxRightUp,isBoxLeftDown,isBoxRightDown)
                );
            
            currColNet = currColNet||boxString||belowString;
            );
        
        currColNet
        );
    
    ans := "";
    for theNet in mingle {sepColumns,boxColumns} do (
        ans = ans|theNet;
        );
    ans^1
    )

-*
DRAWS A TABLOID
net2 SkewTableau := T -> (
    (lam,mu) := shape0 T;

    if #lam == 0 then return "∅";

    (muSmallest, lamLargest) := (min toList mu, max toList lam);
    colWidth := if #entries T == 0 then 1 else max for theBox in entries T list #toString(theBox);
    colWidth = max {colWidth + 2,3};

    ans := "";
    for colIndex from muSmallest to lamLargest do (
        currCol := if colIndex >= mu#0 and colIndex < lam#0 then concatenate(colWidth:"─") else concatenate(colWidth:" ");
        for rowIndex from 0 to #lam-1 do (
            isBox := colIndex >= mu#rowIndex and colIndex < lam#rowIndex;
            isBoxBelow := rowIndex < #lam-1 and colIndex >= mu#(rowIndex+1) and colIndex < lam#(rowIndex+1);
            
            boxString := " ";
            belowString := " ";
            if isBox then (
                boxString = " "|toString((T^rowIndex)#(colIndex-mu#rowIndex))|" ";
                );
            if isBox or isBoxBelow then belowString = "─";
            belowString = concatenate(colWidth:belowString);
            currCol = currCol||boxString||belowString;
            );
        ans = ans|currCol;
        
        
        );
    
    
    ans
    )
*-

tex SkewTableau := T -> (
    -- \usepackage{atableau}
    (lam,mu) := shape0 normalizeNegativeRows T;
    
    isNegativeRow := listNegativeRows T;
    starString := if hasNegativeRow T then ", star style={fill=red!50}" else "";
    
    ans := "\\SkewTableau[skew border, skew boxes"|starString|"] "|toString(toList mu);
    filling := for i from 0 to #lam-1 list (
        currRow := rowEntries(i,T);
        isRed := isNegativeRow#i;
        
        concatenate for theBox in currRow list (
            boxString := toString theBox;
            boxString = if #boxString == 1 then boxString else "{"|boxString|"}";
            if isRed then "*"|boxString else boxString
            )
        );
    ans|toString(filling)
    )

entries SkewTableau := T -> T#values

numcols SkewTableau := T -> (
    (lam,mu) := shape0 normalizeNegativeRows T;
    max(max toList lam - min toList mu,0)
    )

numrows SkewTableau := T -> (
    (lam,mu) := shape0 normalizeNegativeRows T;
    #lam
    )

colRange = method(TypicalValue => Sequence)
colRange SkewTableau := T -> (
    (lam,mu) := shape0 normalizeNegativeRows T;
    (min (toList mu | toList lam)..(max (toList lam | toList mu) - 1))
    )

size SkewTableau := T -> # entries T

toList SkewTableau := T -> (
    for i from 0 to #T#"outerPartition"-1 list T^i
    )

--iterator SkewTableau := T -> iterator entries T

conjugate SkewTableau := T -> (
    if not isYoungTableau T then error "expected inner and outer shapes to be partitions";
    (lam,mu) := shape0 T;

    if #lam == 0 then return T;
    
    lam' := conjugate lam;
    mu' := conjugate mu;
    entryList' := flatten for colIndex from 0 to lam#0-1 list colEntries(colIndex,T);

    skewTableau(lam',mu',entryList')
    )

components SkewTableau := T -> (
    --if hasNegativeRow T then error "tableau has row of negative length";
    (lamOriginal,muOriginal) := shape0 T;
    (lamOriginal,muOriginal) = (toList lamOriginal,toList muOriginal);
    
    (lam,mu) := shape0 normalizeNegativeRows T;
    (lam,mu) = (toList lam,toList mu);

    isNegativeRow := listNegativeRows T;

    isConnectedToNextRow := for i from 0 to numrows T - 2 list (
        if (mu#i <= mu#(i+1) and mu#(i+1) < lam#i and lam#(i+1) > mu#(i+1)) or (mu#(i+1) <= mu#i and mu#i < lam#(i+1) and lam#i > mu#i) then (
            true
            ) else (
            false
            )
        );
    isConnectedToNextRow = append(isConnectedToNextRow,false);

    currComponentStart := 0;
    compRows := for i from 0 to numrows T - 1 list (
        if isConnectedToNextRow#i then continue else (
            compStart := currComponentStart;
            currComponentStart = i + 1;
            (compStart..i)
            )
        );

    for partIndices in compRows list (
        lam' := new Partition from lamOriginal_(toList partIndices);
        mu' := new Partition from muOriginal_(toList partIndices);
        (lam',mu') = alignToZero(lam',mu');
        entryList' := flatten for theIndex in partIndices list rowEntries(theIndex,T);
        if #entryList' == 0 then continue else skewTableau(lam',mu',entryList')
        )
    )

verticalConcatenate = method(TypicalValue => SkewTableau)
verticalConcatenate List := tabList -> (
    lam := new Partition from flatten for T in tabList list toList((shape0 T)#0);
    mu := new Partition from flatten for T in tabList list toList((shape0 T)#1);
    entryList := flatten for T in tabList list entries T;

    skewTableau(lam, mu, entryList)
    )

SkewTableau || SkewTableau := (T1,T2) -> (
    verticalConcatenate {T1,T2}
    )

SkewTableau ++ SkewTableau := (T1,T2) -> (
    (lam1,mu1) := shape0 T1;
    (lam2,mu2) := shape0 T2;
    (entryList1, entryList2) := (entries T1, entries T2);

    lastMu1 := mu1#-1;
    firstLam2 := lam2#0;
    shiftAmount := firstLam2 - lastMu1;

    lam1 = for thePart in lam1 list (thePart + shiftAmount);
    mu1 = for thePart in mu1 list (thePart + shiftAmount);

    lam := new Partition from ((toList lam1)|(toList lam2));
    mu := new Partition from ((toList mu1)|(toList mu2));
    entryList := entryList1|entryList2;

    skewTableau(lam, mu, entryList)
    )

isYoungTableau = method(TypicalValue => Boolean)
isYoungTableau SkewTableau := T -> (
    (lam,mu) := shape0 T;
    (lam,mu) = (toList lam, toList mu);
    
    lam == rsort lam and mu == rsort mu and all(lam|mu, thePart -> thePart >= 0)
    )

isSkew = method(TypicalValue => Boolean)
isSkew SkewTableau := T -> (
    (lam,mu) := shape T;

    #mu != 0
    )

shift = method(TypicalValue => SkewTableau)
shift (SkewTableau,ZZ) := (T,firstRowAmount) -> (
    (lam,mu) := shape0 T;
    
    lam = for i from 0 to #lam-1 list (lam#i+(i+firstRowAmount));
    mu = for i from 0 to #lam-1 list (mu#i+(i+firstRowAmount));

    skewTableau(new Partition from lam, new Partition from mu, entries T)
    )
shift SkewTableau := T -> (
    shift(T,0)
    )

unshift = method(TypicalValue => SkewTableau)
unshift (SkewTableau,ZZ) := (T,firstRowAmount) -> (
    (lam,mu) := shape0 T;
    
    lam = for i from 0 to #lam-1 list (lam#i-(i+firstRowAmount));
    mu = for i from 0 to #lam-1 list (mu#i-(i+firstRowAmount));

    skewTableau(new Partition from lam, new Partition from mu, entries T)
    )
unshift SkewTableau := T -> (
    unshift(T,0)
    )

weight = method(TypicalValue => Sequence)
weight SkewTableau := T -> (
    toSequence for i from 1 to max entries T list number(entries T, theBox -> theBox == i)
    )

indexToPosition = method(TypicalValue => Sequence)
indexToPosition (ZZ,SkewTableau) := (theIndex,T) -> (
    if theIndex < 0 then (
        theIndex = size T + theIndex;
        );
    if theIndex < 0 or theIndex >= size T then error "index out of range";

    (lam,mu) := shape0 normalizeNegativeRows T;
    
    numBoxesSeen := 0;
    for rowIndex from 0 to numRows T - 1 do (
        for colIndex from mu#rowIndex to lam#rowIndex - 1 do (
            if numBoxesSeen == theIndex then return (rowIndex,colIndex);
            numBoxesSeen = numBoxesSeen + 1;
            );
        );
    )

positionToIndex = method(TypicalValue => ZZ)
positionToIndex (Sequence,SkewTableau) := (thePosition,T) -> (
    (rowIndex,colIndex) := thePosition;
    (lam,mu) := shape0 normalizeNegativeRows T;

    if rowIndex < 0 or rowIndex >= #lam or colIndex < mu#rowIndex or colIndex >= lam#rowIndex then error "index out of range";

    numBoxesSeen := 0;
    for theRowIndex from 0 to numRows T - 1 do (
        for theColIndex from mu#theRowIndex to lam#theRowIndex - 1 do (
            if (theRowIndex,theColIndex) == (rowIndex,colIndex) then return numBoxesSeen;
            numBoxesSeen = numBoxesSeen + 1;
            );
        );
    )

maxSSYT = method(TypicalValue => SkewTableau)
maxSSYT (Partition,Partition) := (lam,mu) -> (
    tempT := skewTableau(lam,mu);
    (lam,mu) = shape0 tempT;

    entryList := for entryIndex from 0 to sum toList lam - sum toList mu - 1 list (
        (i,j) := indexToPosition(entryIndex,tempT);
        theCol := tempT_j;
        theColAbove := theCol_(toList(0..i));
        #(delete(null,theColAbove))
        );

    skewTableau(lam,mu,entryList)
    )

minSSYT = method(TypicalValue => SkewTableau)
minSSYT (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    tempT := skewTableau(lam,mu);
    (lam,mu) = shape0 tempT;
    
    entryList := for entryIndex from 0 to sum toList lam - sum toList mu - 1 list (
        (i,j) := indexToPosition(entryIndex,tempT);
        theCol := tempT_j;
        theColBelow := theCol_(toList((i+1)..(#theCol-1)));
        maxEntry - #(delete(null,theColBelow))
        );

    skewTableau(lam,mu,entryList)
    )


addOneSSYT = method(TypicalValue => SkewTableau)
addOneSSYT (SkewTableau,Sequence,SkewTableau) := (T,thePosition,minSSYT) -> (
    if T_thePosition >= minSSYT_thePosition then return null;
    
    (lam,mu) := shape0 T;
    (rowIndex,colIndex) := thePosition;

    if (rowIndex < 0) or (rowIndex >= #lam) then error "index out of range";
    if (colIndex < mu#rowIndex) or (colIndex >= lam#rowIndex) then error "index out of range";

    entryList := new MutableList from entries T;

    for currRowIndex from rowIndex to #T_colIndex-1 do (
        for currColIndex from colIndex to lam#currRowIndex-1 do (
            theIndex := positionToIndex((currRowIndex,currColIndex),T);
            
            currBox := entryList#theIndex;
            
            isBoxLeft := currColIndex > mu#currRowIndex;
            leftBox := if isBoxLeft then (
                leftIndex := positionToIndex((currRowIndex,currColIndex-1),T);
                entryList#leftIndex
                ) else (
                0
                );
            
            isBoxAbove := currRowIndex > 1 and currColIndex >= mu#(currRowIndex-1) and currColIndex < lam#(currRowIndex-1);
            aboveBox := if isBoxAbove then (
                aboveIndex := positionToIndex((currRowIndex-1,currColIndex),T);
                entryList#aboveIndex
                ) else (
                0
                );
            
            if thePosition == (currRowIndex,currColIndex) or currBox < leftBox or currBox <= aboveBox then (
                entryList#theIndex += 1;
                );
            );
        );

    skewTableau(lam,mu,toList entryList)
    )

allSSYT = method(TypicalValue => List)
allSSYT (Partition,Partition,ZZ) := (lam,mu,maxEntry) -> (
    (lam,mu) = shape0(lam,mu);
    (lamList,muList) := (toList lam, toList mu);

    if rsort lamList != lamList or rsort muList != muList then error "expected partitions to be weakly decreasing";
    
    if any(0..(#lam-1), i -> mu#i > lam#i) then return Bag {};

    T := skewTableau(lam,mu);

    if #lam == 0 then return Bag {skewTableau(new Partition from {})};
    if any(colRange T,i -> #colEntries(i,T) > maxEntry) then return Bag {};
    --if all(0..(#lam-1), i -> lam#i == mu#i) then return Bag {skewTableau(lam,mu)};

    maxT := maxSSYT(lam,mu);
    minT := minSSYT(lam,mu,maxEntry);
    ans := {maxT};

    recurse := (theIndex,T) -> (
        newT := addOneSSYT(T,indexToPosition(theIndex,T),minT);
        
        if newT =!= null then (
            ans = append(ans,newT);
            
            for i from 1 to -theIndex do (
                recurse(-i,newT)
                );
            );
        );

    for theIndex from 1 to size T do (
        recurse(-theIndex,maxT);
        );

    Bag ans
    )
allSSYT (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = shape0(lam,mu);
    maxEntry := #lam;
    allSSYT(lam,mu,maxEntry)
    )
allSSYT (Partition,ZZ) := (lam,maxEntry) -> (
    mu := new Partition from {0};
    allSSYT(lam,mu,maxEntry)
    )
allSSYT Partition := lam -> (
    mu := new Partition from {0};
    (lam,mu) = shape0(lam,mu);
    maxEntry := #lam;
    allSSYT(lam,mu,maxEntry)
    )

JTshapes = method(TypicalValue => List)
JTshapes (Partition,Partition) := (lam,mu) -> (
    (lam,mu) = shape0(lam,mu);
    
    rowTableauxTable := new HashTable from for theIndex in unique apply((0,0)..(#lam-1,#lam-1), theInd -> (lam#(theInd#0)+theInd#1+1,mu#(theInd#1)+theInd#0+1)) list (
        (outerLength,innerLength) := theIndex;
        theKey := toString(theIndex);
        theKey => toList allSSYT(new Partition from {outerLength}, new Partition from {innerLength})
        );

    permList := permutations (#lam);
    indexProdList := for thePerm in permList list (
        for i from 0 to #lam-1 list (
            j := thePerm#i;
            (lam#i+j+1,mu#j+i+1)
            )
        );
    
    for theProd in indexProdList list (
        verticalConcatenate for theShape in theProd list skewTableau(new Partition from {theShape#0},new Partition from {theShape#1})
        )
    )
JTshapes Partition := lam -> JTshapes(lam,new Partition from {})

JTtableaux = method(TypicalValue => List)
JTtableaux (Partition,Partition,ZZ) := (lam,mu,N) -> (
    T := skewTableau(lam,mu);
    (lam,mu) = shape0 T;

    rowTableauxTable := new HashTable from for theIndex in unique apply((0,0)..(#lam-1,#lam-1), theInd -> (lam#(theInd#0)+theInd#1+1,mu#(theInd#1)+theInd#0+1)) list (
        (outerLength,innerLength) := theIndex;
        theKey := toString(theIndex);
        theKey => toList allSSYT(new Partition from {outerLength},new Partition from {innerLength},N)
        );
    
    permList := permutations (#lam);
    --signList := for thePerm in permList list (permutationSign thePerm);
    indexProdList := for thePerm in permList list (
        for i from 0 to #lam-1 list (
            j := thePerm#i;
            (lam#i+j+1,mu#j+i+1)
            )
        );

    Bag flatten for j from 0 to #permList-1 list (
        theProd := indexProdList#j;
        
        theKey := toString(theProd#0);
        currProd := rowTableauxTable#theKey;
        for i from 1 to #theProd-1 do (
            theKey = toString(theProd#i);
            currProd = (currProd ** rowTableauxTable#theKey);
            );
        currProd = currProd/deepSplice;
        
        for tabSeq in currProd list (
            wt := flatten for theT in tabSeq list entries theT;
            --wt = toSequence for i from 1 to max wt list number(wt, theNum -> theNum == i);
            --(wt,permList#j,signList#j,tabSeq)
            newT := verticalConcatenate toList tabSeq;
            --(sort entries newT,permList#j,signList#j,newT)
            newT
            )
        )
    )
JTtableaux (Partition,Partition) := (lam,mu) -> (
    JTtableaux(lam,mu,#lam)
    )
