using LinearAlgebra, GenericLinearAlgebra, AbstractAlgebra, SymEngine, Combinatorics, Printf

setprecision(128)
include("ConstructReprSet.jl")
include("DetermineValueMonomial.jl")

#makes a table of all monomials
function GenMonNC(k, dim, t) #Table of size (k*d)^t by 2*t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNC(k, dim, t - 1)
    T = [ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1] ones(Int, size(Ttemp, 1), 1) Ttemp[:, t:2t-2]]
    for i in 1:dim
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
function GenMonNCOnlyK(k, dim, t) #Table of size (k)^t by t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNCOnlyK(k, dim, t - 1)
    T = [ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1]]
    for i in 1:k
        if i != 1
            T = vcat(T, [i * ones(Int, size(Ttemp, 1), 1) Ttemp[:, 1:t-1]])
        end
    end
    return T
end

function GenSmallMomentMat(k, dim, t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNCOnlyK(k, dim, t)
    NrIndices = size(Indices, 1)
    M = Array{SymEngine.Basic}(undef, NrIndices, NrIndices)
    for i in 1:NrIndices, j in 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i)
            monomialKvec = [Indices[i, t:-1:1]; Indices[j, 1:t]]
            monomialIvec = ones(Int, 2 * t)
            M[i, j] = DetermineValueMonomial(dim, monomialIvec, monomialKvec)
        end
    end
    return M
end

function GenSmallMomentMatPlusHalf(k, dim, t, onlyGenerateUpperTriangle=false)
    flush(stdout)
    Indices = GenMonNCOnlyK(k, dim, t)
    NrIndices = size(Indices, 1)
    M = Array{SymEngine.Basic}(undef, NrIndices, NrIndices)
    for i in 1:NrIndices, j in 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i)
            monomialKvec = [Indices[i, t:-1:1]; 1; Indices[j, 1:t]]
            monomialIvec = ones(Int, 2 * t + 1)
            M[i, j] = DetermineValueMonomial(dim, monomialIvec, monomialKvec)
        end
    end
    return M
end

function GenMomentMatPlusHalf(k, dim, t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNC(k, dim, t)
    NrIndices = size(Indices, 1)
    M = Array{SymEngine.Basic}(undef, NrIndices, NrIndices)
    for i in 1:NrIndices, j in 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i)
            monomialIvec = [Indices[i, t:-1:1]; 1; Indices[j, 1:t]]
            monomialKvec = [Indices[i, 2t:-1:t+1]; 1; Indices[j, t+1:2t]]
            M[i, j] = DetermineValueMonomial(dim, monomialIvec, monomialKvec)
        end
    end
    return M
end

function GenMomentMat(k, dim, t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNC(k, dim, t)
    NrIndices = size(Indices, 1)
    M = Array{SymEngine.Basic}(undef, NrIndices, NrIndices)
    for i in 1:NrIndices, j in 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i)
            monomialIvec = [Indices[i, t:-1:1]; Indices[j, 1:t]]
            monomialKvec = [Indices[i, 2t:-1:t+1]; Indices[j, t+1:2t]]
            M[i, j] = DetermineValueMonomial(dim, monomialIvec, monomialKvec)
        end
    end
    return M
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
    # Converts the (BigFloat/Basic) value into a bare string without scientific notation, displaying the
    # given amount of fractional digits and not more, but less if the precision leads to a negative digit.
    #

    result = ""
    if value < 0
        result = "-"
        value *= -1
    end

    intPart = BigInt(floor(value))
    fractPart = value - intPart

    prevFractPart = 0
    tenToKPlusOne = BigInt(10)

    result *= string(intPart) * "."
    for k in 0:fractionalDigits
        newFractPart = BigInt(floor(fractPart * tenToKPlusOne))
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

function MUBWriteSDPA(k, dim, t, option=1)
    manual_epsilon = 0.0000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    println("#####   Generating Moment Matrix...")

    if option == 2
        #option 2: generate full moment matrix for level t+(1/2).
        @time M = GenMomentMatPlusHalf(k, dim, t, true)
        momentBlockSize = size(M, 1)
        optionstring = string("_plushalf")
    elseif option == 3
        #option 3: generate i=1,1,1,1,1,...-part of moment matrix for level t.
        @time M = GenSmallMomentMat(k, dim, t, true)
        momentBlockSize = size(M, 1)
        optionstring = string("_i1part")
    elseif option == 4
        #option 4: generate i=1,1,1,1,1,...-part of moment matrix for level t+.5.
        @time M = GenSmallMomentMatPlusHalf(k, dim, t, true)
        momentBlockSize = size(M, 1)
        optionstring = string("_plushalf", "_i1part")
    else # option ==1
        #This is the DEFAULT, option =1, generate the full moment matrix for level t.
        @time M = GenMomentMat(k, dim, t, true)
        momentBlockSize = size(M, 1)
        optionstring = string("")
    end

    println("##### Collecting the variables in the moment matrix...")
    variables = []
    @time for i in 1:momentBlockSize
        for j in i:momentBlockSize
            symbols = free_symbols(M[i, j])
            if (size(symbols, 1) >= 1)
                for symbol in symbols
                    if !(symbol in variables)
                        push!(variables, symbol)
                    end
                end
            end
        end
    end

    nVars = size(variables, 1)
    nBlocks = 2 * nVars + 1

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    io = open(string("sdp_k$k", "_dim$dim", "_t$t", optionstring, ".dat-s"), "w")
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i in 1:nVars
        print(io, "1 1 ")
    end
    print(io, momentBlockSize, "\n")
    #now print the objective vector
    for i in 1:nVars
        print(io, "-1 ")
    end
    print(io, "\n")
    #now print the constraints -1 <= yi <= 1
    for i in 1:nVars
        blocknumber = 2 * (i - 1) + 1
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io, i, " ", blocknumber, " ", 1, " ", 1, " ", 1)
        println(io, 0, " ", blocknumber, " ", 1, " ", 1, " ", -1)
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io, i, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
        println(io, 0, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for i in 1:momentBlockSize
        for j in i:momentBlockSize
            coefficient = 0
            if (size(free_symbols(M[i, j]), 1) >= 1)
                coefficient = -1 * subs(M[i, j], [r => 0 for r in free_symbols(M[i, j])]...)
            else
                coefficient = -1 * M[i, j]
            end
            if abs(coefficient) > manual_epsilon
                coefficient = coefficient >= 0 ? coefficient + smallbigfloat : coefficient - smallbigfloat
                #println("i ", i , "  j ", j , "  \n" );
                #display(coefficient)
                println(io, 0, " ", nBlocks, " ", i, " ", j, " ", printCoefficient(coefficient))
            end
            for t in 1:nVars
                coefficient = diff(M[i, j], variables[t])
                if abs(coefficient) > manual_epsilon
                    coefficient = coefficient >= 0 ? coefficient + smallbigfloat : coefficient - smallbigfloat
                    println(io, t, " ", nBlocks, " ", i, " ", j, " ", printCoefficient(coefficient))
                end
            end
        end
    end
    close(io)
    println("##### Writing finished.")
end

#WRITES SEPARATE BLOCKS FOR SUBMATRIX GIVEN BY ONE BASIS ELEMENT FROM EACH BASIS.
#USES THE Sk-ACTION (ON FIRST BASIS ELEMENTS ONLY, SEE SECTION 4)
function MUBWriteSDPASymBlockDiagSk(k, dim, t, option=1)
    manual_epsilon = 0.0000000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    println("##### Generating Representative Set...")

    if (option == 2)
        println("#### CASE: k,d,t = ", k, " ", dim, " ", t, "+1/2, i1-part.")
        @time ReprSet, BlockSizes = generateRepresentativeSetPlusHalf(k, t)
        ReprColSet = generateRepresentativeColumnSetPlusHalf(k, t)
        #println("##### Computing Inner Products in Base Block Diagonalization...")
        #@time InnerProducts = ReduceInnerProducts(ReprSet, ReprColSet, 2,true);
        Ivec = ones(Int, 2 * t + 1)

    else  #generate representative set for t-th level
        println("#### CASE: k,d,t = ", k, " ", dim, " ", t)
        @time ReprSet, FirstBlockSizes = generateRepresentativeSet(k, t)
        @time ReprColSet = generateRepresentativeColumnSet(k, t)
        #println("##### Computing Inner Products in Base Block Diagonalization...")
        #@time InnerProducts = ReduceInnerProducts(ReprSet, ReprColSet, 1,true);
        Ivec = ones(Int, 2 * t)
    end

    println("##### Computing Final Block Diagonalization...")
    ReducedBlocks = []
    BlockSizes = []
    MonomialValuesDictionary = Dict()
    aantalblocksK = size(ReprSet, 1)
    @time for i in 1:aantalblocksK
        #BlockForK = InnerProducts[i]
        blockSize = size(ReprSet[i], 1)
        println("block of size ", blockSize)
        push!(BlockSizes, blockSize)
        Block = Array{SymEngine.Basic}(undef, blockSize, blockSize)
        for rowidx in 1:blockSize
            print("row ", rowidx, "            \r")
            reprRowElement = ReprSet[i][rowidx]
            for colidx in 1:blockSize
                reprColElement = ReprColSet[i][colidx]
                if (colidx >= rowidx)
                    #compute the inner product.
                    Block[rowidx, colidx] = 0
                    if (option == 2)
                        InnerProduct = ReduceInnerProduct(reprRowElement, reprColElement, 2)
                    else
                        InnerProduct = ReduceInnerProduct(reprRowElement, reprColElement, 1)
                    end
                    for wordssignK in InnerProduct
                        tempmonoomK = wordssignK[1]
                        if !haskey(MonomialValuesDictionary, tempmonoomK)
                            MonomialValuesDictionary[tempmonoomK] =
                                DetermineValueMonomial(dim, deepcopy(Ivec), deepcopy(tempmonoomK))
                        end
                        Block[rowidx, colidx] += MonomialValuesDictionary[tempmonoomK] * wordssignK[2]
                    end
                end
            end
        end
        ReducedBlocks = push!(ReducedBlocks, Block)
    end

    println("##### Collecting the variables occuring in the blocks...")
    variables = []
    @time for outerindex in 1:size(ReducedBlocks, 1)
        for i in 1:size(ReducedBlocks[outerindex], 1)
            for j in i:size(ReducedBlocks[outerindex], 1)
                symbols = free_symbols(ReducedBlocks[outerindex][i, j])
                if (size(symbols, 1) >= 1)
                    for symbol in symbols
                        if !(symbol in variables)
                            push!(variables, symbol)
                        end
                    end
                end
            end
        end
    end

    println("##### List of variables: ", (variables...))

    nVars = size(variables, 1)

    println("blocksizes = $BlockSizes")
    println("Sum blocksizes = ", sum(BlockSizes))
    nBlocks = 2 * nVars + size(ReducedBlocks, 1)

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    if (option == 2)  ## t+1/2th level
        io = open(string("sdp_k$k", "_dim$dim", "_t$t", "_plushalf_i1part_symmetricblockdiag.dat-s"), "w")
    else
        io = open(string("sdp_k$k", "_dim$dim", "_t$t", "_i1part_symmetricblockdiag.dat-s"), "w")
    end
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i in 1:nVars
        print(io, "1 1 ")
    end
    for i in 1:size(ReducedBlocks, 1)
        print(io, size(ReducedBlocks[i], 1), " ")
    end
    print(io, "\n")
    #now print the objective vector
    for i in 1:nVars
        print(io, "-1 ")
    end
    print(io, "\n")
    #now print the constraints -1 <= yi <= 1
    for i in 1:nVars
        blocknumber = 2 * (i - 1) + 1
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io, i, " ", blocknumber, " ", 1, " ", 1, " ", 1)
        println(io, 0, " ", blocknumber, " ", 1, " ", 1, " ", -1)
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io, i, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
        println(io, 0, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for blockindex in 1:size(ReducedBlocks, 1)
        ArrayBlock = ReducedBlocks[blockindex]
        blocknumber = blockindex + 2 * nVars
        reducedBlockSize = size(ArrayBlock, 1)

        for i in 1:reducedBlockSize
            for j in i:reducedBlockSize
                coefficient = 0
                if (size(free_symbols(ReducedBlocks[blockindex][i, j]), 1) >= 1)
                    coefficient = float(
                        subs(
                            ReducedBlocks[blockindex][i, j],
                            [r => 0 for r in free_symbols(ReducedBlocks[blockindex][i, j])]...,
                        ),
                    )
                else
                    coefficient = float(ReducedBlocks[blockindex][i, j])
                end
                coefficient *= -1 #constant coefficient should be multiplied with -1,  because the matrix is in the form F_1y_1 +..+F_my_m -C
                if abs(coefficient) > manual_epsilon
                    println(io, 0, " ", blocknumber, " ", i, " ", j, " ", coefficient)
                end

                for varnumber in 1:nVars
                    coefficient = float(diff(ReducedBlocks[blockindex][i, j], variables[varnumber]))
                    if abs(coefficient) > manual_epsilon
                        println(io, varnumber, " ", blocknumber, " ", i, " ", j, " ", coefficient)
                    end
                end
            end
        end
    end
    close(io)
    println("##### Writing finished.")
end

#WRITES SEPARATE BLOCKS FOR FULL t-th level of MOMENT MATRIX, USING THE FULL SYMMETRY REDUCTION OF THE WREATH PRODUCT GROUP S_d wr S_k
function MUBWriteSDPASymBlockDiagFULL(k, dim, t, option=1)
    manual_epsilon = 0.0000000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    if (option == 2)
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t, "+1/2.")
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = GeneratePartitionsTableauxFullPlusHalf(k, dim, t)

    else  #generate representative set for t-th level
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t)
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = GeneratePartitionsTableauxFull(k, dim, t)
    end
    println("##### Computing Block Diagonalization...")
    ReducedBlocks = []
    BlockSizes = []
    MonomialValuesDictionary = Dict()
    blockindex = 0
    numzerorows = 0
    @time for (MultiPartition, CorrespondingRows) in BlocksElement
        blockindex += 1
        ReprSetArray = []
        ReprColSetArray = []
        blockSize = size(CorrespondingRows, 1)
        println("Block of size ", blockSize)
        push!(BlockSizes, blockSize)
        println("Generating representative set for this block... ")
        if option == 2 #t+1/2-th level
            for indexobject in CorrespondingRows
                push!(ReprSetArray, RepresentativeFullElementPlusHalf(indexobject))
                push!(ReprColSetArray, RepresentativeColumnElementPlusHalf(indexobject))
            end
        else #t-th level
            for indexobject in CorrespondingRows
                push!(ReprSetArray, RepresentativeFullElement(indexobject))
                push!(ReprColSetArray, RepresentativeColumnElement(indexobject))
            end
        end
        # if blockindex == 3
        #     println("Representative set= ", ReprSetArray)
        # end
        Block = Array{SymEngine.Basic}(undef, blockSize, blockSize)
        Block[1:blockSize, 1:blockSize] .= 0
        println("Computing inner products for this block... ")
        for rowindex in 1:blockSize
            print("row ", rowindex, "            \r")
            for colindex in rowindex:blockSize
                TotalInnerProducts = ReduceInnerProductUsingImub(ReprSetArray[rowindex], ReprColSetArray[colindex])

                for (monomialpair, value) in TotalInnerProducts
                    tempmonoomDim = monomialpair[1]
                    tempmonoomK = monomialpair[2]
                    if !haskey(MonomialValuesDictionary, monomialpair)
                        newmonomial::SymEngine.Basic =
                            DetermineValueMonomial(dim, deepcopy(tempmonoomDim), deepcopy(tempmonoomK))
                        if size(free_symbols(newmonomial), 1) > 0
                            newmonomial = expand(newmonomial)
                        end
                        MonomialValuesDictionary[monomialpair] = newmonomial
                    end
                    Block[rowindex, colindex] += MonomialValuesDictionary[monomialpair] * value
                end
            end
        end
        ReducedBlocks = push!(ReducedBlocks, Block)
    end
    println("##### Collecting the variables occuring in the blocks...")
    variables = []
    @time for outerindex in 1:size(ReducedBlocks, 1)
        for i in 1:size(ReducedBlocks[outerindex], 1)
            for j in i:size(ReducedBlocks[outerindex], 1)
                symbols = free_symbols(ReducedBlocks[outerindex][i, j])
                if (size(symbols, 1) >= 1)
                    for symbol in symbols
                        if !(symbol in variables)
                            push!(variables, symbol)
                        end
                    end
                end
            end
        end
    end

    println("##### List of variables: ", (variables...))

    nVars = size(variables, 1)

    println("blocksizes = $BlockSizes")
    println("Sum blocksizes = ", sum(BlockSizes))
    nBlocks = 2 * nVars + size(ReducedBlocks, 1)

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    if (option == 2)  ## t+1/2th level
        io = open(string("sdp_k$k", "_dim$dim", "_t$t", "_plushalf_FULL_FULLsymmetricblockdiag.dat-s"), "w")
    else
        io = open(string("sdp_k$k", "_dim$dim", "_t$t", "_FULL_FULLsymmetricblockdiag.dat-s"), "w")
    end
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i in 1:nVars
        print(io, "1 1 ")
    end
    for i in 1:size(ReducedBlocks, 1)
        print(io, size(ReducedBlocks[i], 1), " ")
    end
    print(io, "\n")
    #now print the objective vector
    for i in 1:nVars
        print(io, "-1 ")
    end
    print(io, "\n")
    #now print the constraints -1 <= yi <= 1
    for i in 1:nVars
        blocknumber = 2 * (i - 1) + 1
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io, i, " ", blocknumber, " ", 1, " ", 1, " ", 1)
        println(io, 0, " ", blocknumber, " ", 1, " ", 1, " ", -1)
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io, i, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
        println(io, 0, " ", blocknumber + 1, " ", 1, " ", 1, " ", -1)
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for blockindex in 1:size(ReducedBlocks, 1)
        ArrayBlock = ReducedBlocks[blockindex]
        blocknumber = blockindex + 2 * nVars
        reducedBlockSize = size(ArrayBlock, 1)

        for i in 1:reducedBlockSize
            for j in i:reducedBlockSize
                coefficient = 0
                if (size(free_symbols(ReducedBlocks[blockindex][i, j]), 1) >= 1)
                    coefficient = float(
                        subs(
                            ReducedBlocks[blockindex][i, j],
                            [r => 0 for r in free_symbols(ReducedBlocks[blockindex][i, j])]...,
                        ),
                    )
                else
                    coefficient = float(ReducedBlocks[blockindex][i, j])
                end
                coefficient *= -1 #constant coefficient should be multiplied with -1,  because the matrix is in the form F_1y_1 +..+F_my_m -C
                if abs(coefficient) > manual_epsilon
                    println(io, 0, " ", blocknumber, " ", i, " ", j, " ", coefficient)
                end

                for varnumber in 1:nVars
                    coefficient = float(diff(ReducedBlocks[blockindex][i, j], variables[varnumber]))
                    if abs(coefficient) > manual_epsilon
                        println(io, varnumber, " ", blocknumber, " ", i, " ", j, " ", coefficient)
                    end
                end
            end
        end
    end
    close(io)
    println("##### Writing finished.")
end

## TEST: DO WE REALLY GET BLOCK-DIAGONALIZATION?
function MUBTEST(k, dim, t, option=1)
    manual_epsilon = 0.0000000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    if (option == 2)
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t, "+1/2.")
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = GeneratePartitionsTableauxFullPlusHalf(k, dim, t)

    else  #generate representative set for t-th level
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t)
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = GeneratePartitionsTableauxFull(k, dim, t)
    end

    println("##### Computing Block Diagonalization...")
    ReducedBlocks = []
    BlockSizes = []
    MonomialValuesDictionary = Dict()
    blockindex = 0

    ReprSetArray = []
    ReprColSetArray = []
    @time for (MultiPartition, CorrespondingRows) in BlocksElement
        blockindex += 1

        blockSize = size(CorrespondingRows, 1)
        println("Block of size ", blockSize)
        push!(BlockSizes, blockSize)
        println("Generating representative set for this block... ")
        if option == 2 #t+1/2-th level
            for indexobject in CorrespondingRows
                push!(ReprSetArray, RepresentativeFullElementPlusHalfOLD(indexobject))
            end
        else #t-th level
            for indexobject in CorrespondingRows
                push!(ReprSetArray, RepresentativeFullElementOLD(indexobject))
            end
        end
    end

    FullSize = size(ReprSetArray, 1)
    println("fullSize:", FullSize)
    println(BlockSizes)
    BigMat = Array{SymEngine.Basic}(undef, size(ReprSetArray, 1), size(ReprSetArray, 1))
    for rowIdx in 1:FullSize
        for colIdx in 1:FullSize
            TotalInnerProducts = ReduceInnerProductOLD(ReprSetArray[rowIdx], ReprSetArray[colIdx])
            BigMat[rowIdx, colIdx] = 0
            for (monomialpair, value) in TotalInnerProducts
                #println(InnerProduct)
                tempmonoomDim = monomialpair[1]
                tempmonoomK = monomialpair[2]
                # println(tempmonoomDim)
                # println(tempmonoomK)

                if !haskey(MonomialValuesDictionary, monomialpair)
                    newmonomial::SymEngine.Basic = DetermineValueMonomial(dim, deepcopy(tempmonoomDim), deepcopy(tempmonoomK))
                    if size(free_symbols(newmonomial), 1) > 0
                        newmonomial = expand(newmonomial)
                    end
                    MonomialValuesDictionary[monomialpair] = newmonomial
                end
                BigMat[rowIdx, colIdx] += MonomialValuesDictionary[monomialpair] * value
            end
        end
    end
    totalBlockSizes = 0
    println("Display separate blocks ")
    for blockSize in BlockSizes
        display(BigMat[1+totalBlockSizes:blockSize+totalBlockSizes, 1+totalBlockSizes:blockSize+totalBlockSizes])
        for bridx in 1:blockSize
            for bcidx in 1:blockSize
                BigMat[bridx+totalBlockSizes, bcidx+totalBlockSizes] = 0
            end
        end
        totalBlockSizes += blockSize
    end
    println("display full")
    display(BigMat)
end

# MUBWriteSDPASymBlockDiagFULL(5,3,3,2)
# MUBWriteSDPASymBlockDiagFULL(3,3,3)
