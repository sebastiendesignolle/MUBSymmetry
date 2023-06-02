# Helper functions

function AddVariable(VarSet, Dictionary)
    for key in keys(Dictionary)
        if !(key == ([-1], [-1])) && !(key in VarSet)
            push!(VarSet, key)
        end
    end
    return VarSet
end

function ReducedMonomials(d, k, t, reduced=false)
    if !reduced
        PQs = CreatePQiPartitions(d, k, t)
    else
        PQs = CreateRelevantPQiPartitions(d, k, t)
    end
    List = []
    for PQ in PQs
        P = PQ[1]
        Q = PQ[2]
        #Create Kvec and Ivec out of P,Q.
        Kvec = zeros(Int, t)
        Ivec = zeros(Int, t)
        piindex = 0
        for Pi in P
            Kvec[Pi] .= piindex
            piindex += 1

            IvecPart = zeros(Int, size(Pi, 1))
            qiindex = 0
            for Qii in Q[piindex]
                IvecPart[Qii] .= qiindex
                qiindex += 1
            end
            Ivec[Pi] .= IvecPart
        end
        push!(List, (Ivec, Kvec))
    end
    return List
end

function MonomialsSk(k, t)
    Ps = SetPartitionsAtMost(t, k)
    List = []
    for P in Ps
        #Create Kvec out of P
        Kvec = zeros(Int, t)
        piindex = 0
        for Pi in P
            Kvec[Pi] .= piindex
            piindex += 1
        end
        push!(List, Kvec)
    end
    return List
end

function ReducedMonomialsv2(d, k, t)
    PPartitions = SetPartitionsAtMost(t, k)
    MonomialsList = Vector{Tuple{Vector{Int8}, Vector{Int8}}}()
    for P in PPartitions
        QPartitionslist = []
        for Pi in P
            QiPartitions = SetPartitionsAtMost(length(Pi), d)
            QPartitionslist = productQ(QPartitionslist, QiPartitions)
        end
        for Q in QPartitionslist
            Qdef = flatten(Q)
            #Make sure that if P consists of only one part, we still consider Q as a collection [Q_1].
            if size(P, 1) == 1
                Test = Any[]
                push!(Test, Qdef)
                Qdef = Test
            end

            #Create Kvec and Ivec out of P,Qdef.
            Kvec = zeros(Int, t)
            Ivec = zeros(Int, t)
            piindex = 0
            for Pi in P
                Kvec[Pi] .= piindex
                piindex += 1

                IvecPart = zeros(Int, size(Pi, 1))
                qiindex = 0
                for Qii in Qdef[piindex]
                    IvecPart[Qii] .= qiindex
                    qiindex += 1
                end
                Ivec[Pi] .= IvecPart
            end
            #check if (Kvec, Ivec) gives zero row
            givesZeroRow = false
            index1 = 1
            while index1 < length(Ivec)    #if there is a basis which occurs twice subsequently: reduce using Projector-constraint
                index2 = index1 + 1

                if (Kvec[index1] == Kvec[index2] && Ivec[index1] != Ivec[index2])
                    givesZeroRow = true
                    break
                end
                if (Kvec[index1] == Kvec[index2] && Ivec[index1] == Ivec[index2])
                    deleteat!(Kvec, index1)
                    deleteat!(Ivec, index1)
                    index1 -= 1
                end
                index1 += 1
            end

            if (!givesZeroRow)
                push!(MonomialsList, (Ivec, Kvec))
            end
        end
    end
    return unique!(MonomialsList)
end

function minimumcyclicpart(v)
    v = make_partition(v)
    outputvector = deepcopy(v)
    for i in 1:length(v)
        vtemp = make_partition([v[i+1:end]; v[1:i]])
        if (isless(vtemp, outputvector))
            outputvector = vtemp
        end
    end
    return outputvector
end

function minimumcyclicpartIK(Ivec, Kvec)
    v = make_partition(Kvec)
    outputKvector = deepcopy(v)
    outputIvector = deepcopy(Ivec)
    for i in 1:length(v)
        Ktemp = make_partition([v[i+1:end]; v[1:i]])
        Itemp = renumberIdependingOnK([Ivec[i+1:end]; Ivec[1:i]], Ktemp)
        if isless([Ktemp, Itemp], [outputKvector, outputIvector])
            outputKvector = Ktemp
            outputIvector = Itemp
        end
    end
    return outputIvector, outputKvector
end

function minimumLexico(Ivec, Kvec)
    outputKvector = deepcopy(Kvec)
    outputIvector = deepcopy(Ivec)
    (tempI, tempK) = minimumcyclicpartIK(outputIvector, outputKvector)
    (tempI2, tempK2) = minimumcyclicpartIK(outputIvector[end:-1:1], outputKvector[end:-1:1])
    if isless([tempK, tempI], [tempK2, tempI2])
        outputKvector = tempK
        outputIvector = tempI
    else
        outputKvector = tempK2
        outputIvector = tempI2
    end
    return outputIvector, outputKvector
end

function renumberIdependingOnK(Ivec, Kvec)
    for i in 0:length(Kvec)/2
        PositionsToChange = findall(x -> x == i, Kvec)
        Ivec[PositionsToChange] = make_partition(Ivec[PositionsToChange])
    end
    return Ivec
end

function make_partition(J)  #returns lexicographically smallest element of S_n-orbit of word in {0,..,n-1}^t
    #For example: make_partition([3, 3, 2, 1]) = [0,0,1,2]
    originalJ = deepcopy(J)
    n = length(J)
    toberenumbered = collect(1:n) #vector of all indices

    countrenumbered = 0
    newentry = 0

    while countrenumbered < n
        renumberthisloop = findall(x -> x == originalJ[toberenumbered[1]], originalJ)
        J[renumberthisloop] .= newentry

        countrenumbered += length(renumberthisloop)
        setdiff!(toberenumbered, renumberthisloop)
        newentry += 1
    end

    return J
end

#generate array of set partitions of [t] into at most r parts;
function SetPartitionsAtMost(t, r)
    startset = collect(partitions(collect(1:t), 1))

    for j in 2:r
        startset = append!(startset, collect(partitions(collect(1:t), j)))
    end

    return startset
end

# Creates a list with all pairs (P,Q) where P is a set partition of [t] in at most k parts, and Q is a tuple of set partitions (in at most d parts) that refines P
function CreatePQiPartitions(d, k, t)
    PPartitions = SetPartitionsAtMost(t, k)
    PWithQList = Tuple{Vector{Vector{Int8}}, Vector{Vector{Vector{Int8}}}}[]
    for P in PPartitions
        QPartitionslist = []
        for Pi in P
            QiPartitions = SetPartitionsAtMost(length(Pi), d)
            QPartitionslist = productQ(QPartitionslist, QiPartitions)
        end
        for Q in QPartitionslist
            Qdef = flatten(Q)
            #Make sure that if P consists of only one part, we still consider Q as a collection [Q_1].
            if size(P, 1) == 1
                Test = Any[]
                push!(Test, Qdef)
                Qdef = Test
            end
            Qdef = convert(Vector{Vector{Vector{Int8}}}, Qdef)
            push!(PWithQList, (P, Qdef))
        end
    end
    return PWithQList
end

# only create pairs (P,Q) that do not give rise to zero rows
function CreateRelevantPQiPartitions(d, k, t)
    PPartitions = SetPartitionsAtMost(t, k)
    PWithQList = Tuple{Vector{Vector{Int8}}, Vector{Vector{Vector{Int8}}}}[]
    for P in PPartitions
        QPartitionslist = []
        for Pi in P
            QiPartitions = SetPartitionsAtMost(length(Pi), d)
            QPartitionslist = productQ(QPartitionslist, QiPartitions)
        end
        for Q in QPartitionslist
            Qdef = flatten(Q)
            #Make sure that if P consists of only one part, we still consider Q as a collection [Q_1].
            if size(P, 1) == 1
                Test = Any[]
                push!(Test, Qdef)
                Qdef = Test
            end

            #Create Kvec and Ivec out of P,Qdef.
            Kvec = zeros(Int, t)
            Ivec = zeros(Int, t)
            piindex = 0
            for Pi in P
                Kvec[Pi] .= piindex
                piindex += 1

                IvecPart = zeros(Int, size(Pi, 1))
                qiindex = 0
                for Qii in Qdef[piindex]
                    IvecPart[Qii] .= qiindex
                    qiindex += 1
                end
                Ivec[Pi] .= IvecPart
            end
            #check if (Kvec, Ivec) gives zero row
            givesZeroRow = false
            for index1 in 1:t-1    #if there is a basis which occurs twice subsequently: reduce using Projector-constraint
                index2 = index1 + 1

                if (Kvec[index1] == Kvec[index2] && Ivec[index1] != Ivec[index2])
                    givesZeroRow = true
                end
            end

            if (!givesZeroRow)
                Qdef = convert(Vector{Vector{Vector{Int8}}}, Qdef)
                push!(PWithQList, (P, Qdef))
            end
        end
    end
    return PWithQList
end

# only create pairs (P,Q) that do not give rise to zero rows and reduce using projector constraint AND MUB-constraint
function CreateRelevantPQiPartitionsV2(d, k, t)
    PPartitions = SetPartitionsAtMost(t, k)
    PWithQList = Tuple{Vector{Vector{Int8}}, Vector{Vector{Vector{Int8}}}}[]
    WordDict = Dict()
    for P in PPartitions
        QPartitionslist = []
        for Pi in P
            QiPartitions = SetPartitionsAtMost(length(Pi), d)
            QPartitionslist = productQ(QPartitionslist, QiPartitions)
        end
        for Q in QPartitionslist
            Qdef = flatten(Q)
            #Make sure that if P consists of only one part, we still consider Q as a collection [Q_1].
            if size(P, 1) == 1
                Test = Any[]
                push!(Test, Qdef)
                Qdef = Test
            end

            #Create Kvec and Ivec out of P,Qdef.
            Kvec = zeros(Int, t)
            Ivec = zeros(Int, t)
            piindex = 0
            for Pi in P
                Kvec[Pi] .= piindex
                piindex += 1

                IvecPart = zeros(Int, size(Pi, 1))
                qiindex = 0
                for Qii in Qdef[piindex]
                    IvecPart[Qii] .= qiindex
                    qiindex += 1
                end
                Ivec[Pi] .= IvecPart
            end
            #check if (Kvec, Ivec) gives zero row
            givesZeroRow = false
            index1 = 1
            while index1 < length(Ivec)    #if there is a basis which occurs twice subsequently: reduce using Projector-constraint
                index2 = index1 + 1
                index3 = index1 + 2
                if (Kvec[index1] == Kvec[index2] && Ivec[index1] != Ivec[index2])
                    givesZeroRow = true
                    break
                end
                if (Kvec[index1] == Kvec[index2] && Ivec[index1] == Ivec[index2])
                    deleteat!(Kvec, index1)
                    deleteat!(Ivec, index1)
                    index1 -= 1
                elseif (index3 <= length(Ivec) && Kvec[index1] == Kvec[index3] && Ivec[index1] == Ivec[index3]) ##reduce X_{index1,k} X_{index2,l} X{index1,k} 
                    deleteat!(Kvec, index2)
                    deleteat!(Ivec, index2)
                    index1 -= 1
                end
                index1 += 1
            end

            Ivec = renumberIdependingOnK(Ivec, Kvec)
            Kvec = make_partition(Kvec)

            if (!givesZeroRow)
                Qdef = convert(Vector{Vector{Vector{Int8}}}, Qdef)
                WordDict[(Ivec, Kvec)] = (P, Qdef)
            end
        end
    end
    PWithQList = []
    for (monomial, PWithQ) in WordDict
        push!(PWithQList, PWithQ)
    end
    print(size(PWithQList))
    return PWithQList
end

# Returns the lexicographically smallest element corresponding to Ivec, taking into account the KPartition (applies make_partition to each set Pi in KPartition)
function renumberIdependingOnKPartition(Ivec, KPartition)
    for Pi in KPartition
        Ivec[Pi] = make_partition(Ivec[Pi])
    end
    return Ivec
end

#makes a table of all monomials
function GenMonNC(d, k, t) #Table of size (k*d)^t by 2*t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNC(d, k, t - 1)
    T = [ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1] ones(Int, size(Ttemp, 1), 1) Ttemp[:, t:2t-2]]
    for i in 1:d
        for j in 1:k
            if i != 1 || j != 1
                T = vcat(
                    T,
                    [i * ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1] j * ones(Int, size(Ttemp, 1), 1) Ttemp[:, t:2t-2]],
                )
            end
        end
    end
    return T
end

#makes a table of all monomials
function GenMonNCOnlyK(d, k, t) #Table of size (k)^t by t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNCOnlyK(d, k, t - 1)
    T = [ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1]]
    for i in 1:k
        if i != 1
            T = vcat(T, [i * ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1]])
        end
    end
    return T
end

function printCoefficient(coefficient)
    printprecision = 20
    coefficientstring = toString(coefficient, printprecision)
    coefficientstring = coefficientstring[1:min(sizeof(coefficientstring), printprecision)]
    #delete trailing zeros
    if (occursin(".", coefficientstring))
        digit = coefficientstring[end]
        while (cmp(digit, '0') == 0 || cmp(digit, '.') == 0)
            coefficientstring = chop(coefficientstring)
            digit = coefficientstring[end]
        end
    end
    return coefficientstring
end

function toString(value, fractionalDigits::Integer)
    # Source: https://www.mail-archive.com/julia-users@googlegroups.com/msg28174.html
    #
    # Converts the (Rational{Int}/Basic) value into a bare string without scientific notation, displaying the
    # given amount of fractional digits and not more, but less if the precision leads to a negative digit.
    #

    result = ""
    if value < 0
        result = "-"
        value *= -1
    end

    intPart = Int(floor(value))
    fractPart = value - intPart

    prevFractPart = 0
    tenToKPlusOne = Int(10)

    result *= string(intPart) * "."
    for k in 0:fractionalDigits
        newFractPart = Int(floor(fractPart * tenToKPlusOne))
        digit = Int((newFractPart - prevFractPart * 10) % 10)

        if digit < 0
            # happens sometimes if the precision is reached, so it doesn't make sense to analyze it further
            break
        end

        result *= string(digit)
        prevFractPart = newFractPart
        tenToKPlusOne *= 10
    end

    return result
end
