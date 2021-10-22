using LinearAlgebra, GenericLinearAlgebra
using SymEngine, Combinatorics
using Printf

setprecision(128)
include("DetermineValueMonomialmax11.jl")


function GenMonNC(k,dim,t) #Table of size (k*d)^t by 2*t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNC(k,dim,t-1)
    T = [ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1] ones(Int,size(Ttemp,1),1) Ttemp[:,t:2t-2]]
    for i = 1:dim
        for j = 1:k
            if i != 1 || j != 1
                T = vcat(T, [i*ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1] j*ones(Int,size(Ttemp,1),1) Ttemp[:,t:2t-2]])
            end
        end
    end
    return T
end

function GenMonNC12(k,dim,t) #Table of size (k*2)^t by 2*t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNC12(k,dim,t-1)
    T = [ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1] ones(Int,size(Ttemp,1),1) Ttemp[:,t:2t-2]]
    for i = 1:2
        for j = 1:k
            if i != 1 || j != 1
                T = vcat(T, [i*ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1] j*ones(Int,size(Ttemp,1),1) Ttemp[:,t:2t-2]])
            end
        end
    end
    return T
end


function GenMonNCOnlyK(k,dim,t) #Table of size (k)^t by t
    if t == 0
        return [0]
    end
    Ttemp = GenMonNCOnlyK(k,dim,t-1)
    T = [ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1]]
    for i = 1:k
            if i != 1
                T = vcat(T, [i*ones(Int,size(Ttemp,1),1) Ttemp[:,1:t-1]])
            end
    end
    return T
end


function GenMonNCOnlyKPermutations(t) #Table of size t! by t
    if t == 0
        return [0]
    end
    Ttemp = collect(permutations(Array((1:t))));
    T=(Ttemp[1,:]...)'
    for i = 2:size(Ttemp,1)
        T = vcat(T, (Ttemp[i,:]...)')
    end
    return T
end


function GenMicroPermutationsMomentMat(k,dim,t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNCOnlyKPermutations(t)
    NrIndices = size(Indices,1)
    M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)
    for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialKvec = [Indices[i,t:-1:1];1; Indices[j,1:t]]
            monomialIvec = ones(Int,2*t+1)
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
    end
    return M
end



function GenSmallMomentMat(k,dim,t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNCOnlyK(k,dim,t)
    NrIndices = size(Indices,1)
    M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)
    for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialKvec = [Indices[i,t:-1:1]; Indices[j,1:t]]
            monomialIvec = ones(Int,2*t)
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
    end
    return M
end


function GenSmallMomentMatPlusHalf(k,dim,t, onlyGenerateUpperTriangle=false)
    flush(stdout)
    Indices = GenMonNCOnlyK(k,dim,t)
    NrIndices = size(Indices,1)
    M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)
    for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialKvec = [Indices[i,t:-1:1];1; Indices[j,1:t]]
            monomialIvec = ones(Int,2*t+1)
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
    end
    return M
end

function GenSmall12MomentMatPlusHalf(k,dim,t, onlyGenerateUpperTriangle=false)
    flush(stdout)
    Indices = GenMonNC12(k,dim,t)
    NrIndices = size(Indices,1)
    M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)

    for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialIvec = [Indices[i,t:-1:1]; 1; Indices[j,1:t]]
            monomialKvec = [Indices[i,2t:-1:t+1];1; Indices[j,t+1:2t]]
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
    end
    return M
end


function GenMomentMatPlusHalf(k,dim,t, onlyGenerateUpperTriangle=false)
     Indices = GenMonNC(k,dim,t)
     NrIndices = size(Indices,1)
     M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)
     for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialIvec = [Indices[i,t:-1:1];1; Indices[j,1:t]]
            monomialKvec = [Indices[i,2t:-1:t+1];1; Indices[j,t+1:2t]]
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
     end
     return M
 end

function GenMomentMat(k,dim,t, onlyGenerateUpperTriangle=false)
    Indices = GenMonNC(k,dim,t)
    NrIndices = size(Indices,1)
    M = Array{SymEngine.Basic}(undef,NrIndices,NrIndices)
    for i = 1:NrIndices, j = 1:NrIndices
        if (!onlyGenerateUpperTriangle || j >= i )
            monomialIvec = [Indices[i,t:-1:1]; Indices[j,1:t]]
            monomialKvec = [Indices[i,2t:-1:t+1]; Indices[j,t+1:2t]]
            M[i,j] = bepaalwaardemonoom(dim,monomialIvec,monomialKvec)
        end
    end
    return M
end

function printCoefficient(coefficient)
    printprecision = 20;
    coefficientstring =  toString(coefficient,printprecision);
    coefficientstring = coefficientstring[1:min(sizeof(coefficientstring),printprecision)]
    #delete trailing zeros
    if (occursin(".", coefficientstring))
        digit = coefficientstring[end];
        while (cmp(digit,'0')==0 ||cmp(digit,'.')==0)
            coefficientstring = chop(coefficientstring)
            digit=coefficientstring[end];
        end
    end
    return coefficientstring;
end

function toString(value, fractionalDigits::Integer)
    # functie van internet
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
        digit = Int( (newFractPart - prevFractPart * 10) % 10 )

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

function MUBWriteSDPA(k,dim,t, option=1)
    manual_epsilon = 0.0000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    println("#####   Generating Moment Matrix...")

    if option ==2
        #option 2: generate full moment matrix for level t+(1/2).
        @time M = GenMomentMatPlusHalf(k,dim,t,true)
        momentBlockSize = size(M,1);
        optionstring = string("_plushalf")
    elseif option ==3
        #option 3: generate i=1,1,1,1,1,...-part of moment matrix for level t.
        @time M = GenSmallMomentMat(k,dim,t,true)
        momentBlockSize = size(M,1);
        optionstring = string("_i1part")
    elseif option ==4
        #option 4: generate i=1,1,1,1,1,...-part of moment matrix for level t+.5.
        @time M = GenSmallMomentMatPlusHalf(k,dim,t,true)
        momentBlockSize = size(M,1);
        optionstring = string("_plushalf","_i1part")
    elseif option ==5
        #option 5: generate I=i1,i2,... with all i_j \in {1,2}-part of moment matrix for level t+.5.
	@time M = GenSmall12MomentMatPlusHalf(k,dim,t, true)
        momentBlockSize = size(M,1);
        optionstring = string("_plushalf","_I12")
    elseif option ==6
        #option 5: generate I=i1,i2,... with all i_j \in {1,..,k}-part (with the last i=1) and all k_j also in {1,..,k} (with the last k=1,2) of moment matrix for level t+.5.
	@time M = GenSmall1kMomentMatPlusHalf(k,dim,t, true)
        momentBlockSize = size(M,1);
        optionstring = string("_plushalf","_i1kpart")
    elseif option ==7
        #option 4: generate permutations part of i=1,1,1,1,1,...-part of moment matrix for level t+.5.
        @time M = GenMicroPermutationsMomentMat(k,dim,t,true)
        momentBlockSize = size(M,1);
        optionstring = string("_plushalf","_i1permutationspart")
    else # option ==1
        #This is the DEFAULT, option =1, generate the full moment matrix for level t.
        @time M = GenMomentMat(k,dim,t,true)
        momentBlockSize = size(M,1);
        optionstring = string("")
    end


    println("##### Collecting the variables in the moment matrix...")
    variables = [];
    @time for i=1:momentBlockSize
            for j=i:momentBlockSize
                symbols = free_symbols(M[i,j])
                if (size(symbols,1)>=1)
                    for symbol in symbols
                        if !(symbol in variables)
                            push!(variables,symbol);
                        end
                    end
                end
            end
    end

    nVars= size(variables,1)
    nBlocks = 2*nVars + 1;

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    io = open(string("sdp_k$k","_dim$dim","_t$t",optionstring,".dat-s"), "w")
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i=1:nVars
        print(io, "1 1 ")
    end
    print(io,momentBlockSize,"\n")
    #now print the objective vector
    for i=1:nVars
        print(io, "-1 ")
    end
    print(io,"\n");
    #now print the constraints -1 <= yi <= 1
    for i=1:nVars
        blocknumber = 2*(i-1)+1;
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io,i," ",blocknumber," ",1, " ",1 , " ",1 )
        println(io,0," ",blocknumber," ",1, " ",1 , " ",-1 )
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io,i," ",blocknumber+1," ",1, " ",1 , " ",-1 )
        println(io,0," ",blocknumber+1," ",1, " ",1 , " ",-1 )
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for i=1:momentBlockSize
        for j=i:momentBlockSize
            coefficient=0
            if (size(free_symbols(M[i,j]),1)>=1)
                coefficient = -1*subs(M[i,j], [r => 0 for r in free_symbols(M[i,j])]...)
            else
                coefficient = -1*M[i,j]
            end
            if abs(coefficient)> manual_epsilon
                coefficient = coefficient >=0 ? coefficient+smallbigfloat : coefficient-smallbigfloat;
		#println("i ", i , "  j ", j , "  \n" );
		#display(coefficient)
                println(io,0," ",nBlocks," ",i, " ",j , " ", printCoefficient(coefficient))
            end
            for t=1:nVars
                coefficient =  diff(M[i,j],variables[t]);
                if abs(coefficient)> manual_epsilon
                    coefficient = coefficient >=0 ? coefficient+smallbigfloat : coefficient-smallbigfloat;
                    println(io,t," ",nBlocks," ",i, " ",j , " ",  printCoefficient(coefficient))
                end
            end
        end
    end
    println("##### Writing finished.")
end


include("NonCommutativeRepresentativeSet25-2.jl")
#NEW VERSION, WRITES SEPARATE BLOCKS FOR I=1-part of t-th level of MOMENT MATRIX, USING THE SYMMETRY REDUCTION!
function MUBWriteSDPASymBlockDiag(k,dim,t,option=1)
    manual_epsilon = 0.0000000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")

    println("##### Generating Representative Set...")

    if (option ==2)
        println("#### CASE: k,d,t = ", k, " ", dim, " ", t , "+1/2, i1-part.")
        @time ReprSet, BlockSizes = generateRepresentativeSetPlusHalf(k,t)
        ReprColSet= generateRepresentativeColumnSetPlusHalf(k,t)
        #println("##### Computing Inner Products in Base Block Diagonalization...")
        #@time InnerProducts = ReduceInnerProducts(ReprSet, ReprColSet, 2,true);
        Ivec = ones(Int,2*t+1)
    
    else  #generate representative set for t-th level
        println("#### CASE: k,d,t = ", k, " ", dim, " ", t)
        @time ReprSet, FirstBlockSizes = generateRepresentativeSet(k,t)
        @time ReprColSet= generateRepresentativeColumnSet(k,t)
        #println("##### Computing Inner Products in Base Block Diagonalization...")
        #@time InnerProducts = ReduceInnerProducts(ReprSet, ReprColSet, 1,true);
        Ivec = ones(Int,2*t)
    end

    println("##### Computing Final Block Diagonalization...")
    ReducedBlocks=[];
    BlockSizes=[];

    MonomialValuesDictionary = Dict()

    aantalblocksK = size(ReprSet,1)
    @time for i=1: aantalblocksK 
        #BlockForK = InnerProducts[i]
        blockSize=size(ReprSet[i],1)
        println("block of size ", blockSize )
        push!(BlockSizes,blockSize)
        Block = Array{SymEngine.Basic}(undef,blockSize,blockSize)
        for rowidx = 1:blockSize
	    println("row ",rowidx)
	    reprRowElement = ReprSet[i][rowidx]	
            for colidx = 1:blockSize
	            reprColElement = ReprColSet[i][colidx]
                    if (colidx >=rowidx)
                            #compute the inner product.
                            Block[rowidx,colidx]=0;
			    if (option == 2 )
			    	InnerProduct = ReduceInnerProduct(reprRowElement,reprColElement,2)	
			    else
			    	InnerProduct = ReduceInnerProduct(reprRowElement,reprColElement,1)
			    end
                            for wordssignK in InnerProduct
                                tempmonoomK=wordssignK[1];
                                if !haskey(MonomialValuesDictionary,tempmonoomK)
                                    MonomialValuesDictionary[tempmonoomK] = bepaalwaardemonoom(dim,deepcopy(Ivec),deepcopy(tempmonoomK))
                                end
                            Block[rowidx,colidx] +=  MonomialValuesDictionary[tempmonoomK]*wordssignK[2]
                            end
                    end
            end
        end
            ReducedBlocks = push!(ReducedBlocks,Block);
#	    empty!(MonomialValuesDictionary);
    end

    println("##### Collecting the variables occuring in the blocks...")
    variables = [];
    @time for outerindex=1:size(ReducedBlocks,1)
         for i=1:size(ReducedBlocks[outerindex],1)
            for j=i:size(ReducedBlocks[outerindex],1)
                symbols = free_symbols(ReducedBlocks[outerindex][i,j])
                if (size(symbols,1)>=1)
                    for symbol in symbols
                        if !(symbol in variables)
                            push!(variables,symbol);
                        end
                    end
                end
            end
        end
    end

    println("##### List of variables: ", (variables...))
    
    nVars= size(variables,1)

    println("blocksizes = $BlockSizes")
    println("Sum blocksizes = ", sum(BlockSizes));
    nBlocks = 2*nVars + size(ReducedBlocks,1);
    

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    if (option ==2)  ## t+1/2th level
        io = open(string("sdp_k$k","_dim$dim","_t$t","_plushalf_i1part_symmetricblockdiag.dat-s"), "w")
    else
        io = open(string("sdp_k$k","_dim$dim","_t$t","_i1part_symmetricblockdiag.dat-s"), "w")
    end
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i=1:nVars
        print(io, "1 1 ")
    end
    for i=1:size(ReducedBlocks,1)
        print(io, size(ReducedBlocks[i],1)," ")
    end
    print(io,"\n")
    #now print the objective vector
    for i=1:nVars
        print(io, "-1 ")
    end
    print(io,"\n");
    #now print the constraints -1 <= yi <= 1
    for i=1:nVars
        blocknumber = 2*(i-1)+1;
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io,i," ",blocknumber," ",1, " ",1 , " ",1 )
        println(io,0," ",blocknumber," ",1, " ",1 , " ",-1 )
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io,i," ",blocknumber+1," ",1, " ",1 , " ",-1 )
        println(io,0," ",blocknumber+1," ",1, " ",1 , " ",-1 )
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for blockindex = 1: size(ReducedBlocks,1)
        ArrayBlock = ReducedBlocks[blockindex]
        blocknumber = blockindex + 2*nVars
        reducedBlockSize = size(ArrayBlock,1)

        for i=1:reducedBlockSize
            for j=i:reducedBlockSize
                    coefficient = 0;
                    if (size(free_symbols(ReducedBlocks[blockindex][i,j]),1)>=1)
                        coefficient = float(subs(ReducedBlocks[blockindex][i,j], [r => 0 for r in free_symbols(ReducedBlocks[blockindex][i,j])]...))
                    else
                        coefficient = float(ReducedBlocks[blockindex][i,j])
                    end
                    coefficient *= -1 #constant coefficient should be multiplied with -1,  because the matrix is in the form F_1y_1 +..+F_my_m -C 
                    if abs(coefficient)> manual_epsilon
		        println(io,0," ",blocknumber," ",i, " ",j , " ", coefficient)
                    end

                    for varnumber =1:nVars
                                coefficient =  float(diff(ReducedBlocks[blockindex][i,j],variables[varnumber]))
                            if abs(coefficient)> manual_epsilon
				println(io,varnumber," ",blocknumber," ",i, " ",j , " ", coefficient)
                            end
                    end
            end
        end
    end
    println("##### Writing finished.")
end


#@time MUBWriteSDPASymBlockDiag(5,6,5)

#NEW VERSION, WRITES SEPARATE BLOCKS FOR FULL t-th level of MOMENT MATRIX, USING THE FULL SYMMETRY REDUCTION OF THE WREATH PRODUCT GROUP S_d wr S_k
function MUBWriteSDPASymBlockDiagFULL(k,dim,t, option=1)
    manual_epsilon = 0.0000000000000001  #if smaller than this epsilon, consider coefficient to be zero.
    smallbigfloat = BigFloat("0.0000000000000000000000000000001")


    if (option ==2)
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t , "+1/2.")
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = BlockGroottesFullProblemPlusHalf(k,dim,t)
    
    else  #generate representative set for t-th level
        println("#### FULL SYMMETRY, CASE: k,d,t = ", k, " ", dim, " ", t)
        println("##### Generating SetPartitions, Compositions, (Multi)Partitions and Tableaux...")
        @time BlocksElement = BlockGroottesFullProblem(k,dim,t)
    end


    println("##### Computing Block Diagonalization...")
    ReducedBlocks=[];
    BlockSizes=[];
    MonomialValuesDictionary = Dict()
    @time for (MultiPartition, CorrespondingRows) in BlocksElement
        ReprSetArray=[]
        ReprColSetArray=[]
        blockSize = size(CorrespondingRows,1)
        println("Block of size ",blockSize)
        push!(BlockSizes, blockSize)
        println("Generating representative set for this block... ")
        if option==2 #t+1/2-th level 
            for indexobject in CorrespondingRows
                push!(ReprSetArray,RepresentativeFullElementPlusHalf(indexobject))
                push!(ReprColSetArray,RepresentativeColumnElementPlusHalf(indexobject))
            end
        else #t-th level 
            for indexobject in CorrespondingRows
                push!(ReprSetArray,RepresentativeFullElement(indexobject))
                push!(ReprColSetArray,RepresentativeColumnElement(indexobject))
            end
        end
        Block = Array{SymEngine.Basic}(undef,blockSize,blockSize)
        println("Computing inner products for this block... ")
        for rowindex =1:blockSize
            println("rij ",rowindex)
            for colindex=rowindex:blockSize
                #compute the inner product.
                (InnerProductsK, InnerProductsD) = ReduceInnerProductFULL(ReprSetArray[rowindex], ReprColSetArray[colindex])
                TotalInnerProducts= ReduceInnerProductFurther(InnerProductsK, InnerProductsD);

                #println("size total inner products ", size(TotalInnerProducts,1))
                Block[rowindex,colindex]=0;
                for (monomialpair,value) in TotalInnerProducts 
                    #println(InnerProduct)
                    tempmonoomDim=monomialpair[1]
                    tempmonoomK=monomialpair[2]
                    
                    # println(tempmonoomDim)
                    # println(tempmonoomK)
                    if !haskey(MonomialValuesDictionary,monomialpair)
                        MonomialValuesDictionary[monomialpair] = bepaalwaardemonoom(dim,deepcopy(tempmonoomDim),deepcopy(tempmonoomK))
                    end
                    Block[rowindex,colindex] +=  MonomialValuesDictionary[monomialpair]*value
                end
            end
        end
        ReducedBlocks = push!(ReducedBlocks,Block);
    end

    println("##### Collecting the variables occuring in the blocks...")
    variables = [];
    @time for outerindex=1:size(ReducedBlocks,1)
         for i=1:size(ReducedBlocks[outerindex],1)
            for j=i:size(ReducedBlocks[outerindex],1)
                symbols = free_symbols(ReducedBlocks[outerindex][i,j])
                if (size(symbols,1)>=1)
                    for symbol in symbols
                        if !(symbol in variables)
                            push!(variables,symbol);
                        end
                    end
                end
            end
        end
    end

    println("##### List of variables: ", (variables...))

    nVars= size(variables,1)

    println("blocksizes = $BlockSizes")
    println("Sum blocksizes = ", sum(BlockSizes));
    nBlocks = 2*nVars + size(ReducedBlocks,1);
    

    println("##### Writing the SDP...")
    ###start writing SDP file in SDPA-format (.dat-s)
    if (option ==2)  ## t+1/2th level
        io = open(string("sdp_k$k","_dim$dim","_t$t","_plushalf_FULL_FULLsymmetricblockdiag.dat-s"), "w")
    else
        io = open(string("sdp_k$k","_dim$dim","_t$t","_FULL_FULLsymmetricblockdiag.dat-s"), "w")
    end
    #print the number of variables, the number of blocks and the block sizes.
    println(io, nVars)
    println(io, nBlocks)
    for i=1:nVars
        print(io, "1 1 ")
    end
    for i=1:size(ReducedBlocks,1)
        print(io, size(ReducedBlocks[i],1)," ")
    end
    print(io,"\n")
    #now print the objective vector
    for i=1:nVars
        print(io, "-1 ")
    end
    print(io,"\n");
    #now print the constraints -1 <= yi <= 1
    for i=1:nVars
        blocknumber = 2*(i-1)+1;
        #constraint yi - (-1) >=0, i.e. yi >=-1
        println(io,i," ",blocknumber," ",1, " ",1 , " ",1 )
        println(io,0," ",blocknumber," ",1, " ",1 , " ",-1 )
        #constraint -yi -(-1) >=0, i.e. yi <=1
        println(io,i," ",blocknumber+1," ",1, " ",1 , " ",-1 )
        println(io,0," ",blocknumber+1," ",1, " ",1 , " ",-1 )
    end
    #now print the constraint that the moment matrix must be p.s.d. (note, the block number is nBlocks)
    @time for blockindex = 1: size(ReducedBlocks,1)
        ArrayBlock = ReducedBlocks[blockindex]
        blocknumber = blockindex + 2*nVars
        reducedBlockSize = size(ArrayBlock,1)

        for i=1:reducedBlockSize
            for j=i:reducedBlockSize
                    coefficient = 0;
                    if (size(free_symbols(ReducedBlocks[blockindex][i,j]),1)>=1)
                        coefficient = float(subs(ReducedBlocks[blockindex][i,j], [r => 0 for r in free_symbols(ReducedBlocks[blockindex][i,j])]...))
                    else
                        coefficient = float(ReducedBlocks[blockindex][i,j])
                    end
                    coefficient *= -1 #constant coefficient should be multiplied with -1,  because the matrix is in the form F_1y_1 +..+F_my_m -C 
                    if abs(coefficient)> manual_epsilon
                            println(io,0," ",blocknumber," ",i, " ",j , " ", coefficient)
                    end

                    for varnumber =1:nVars
                                coefficient =  float(diff(ReducedBlocks[blockindex][i,j],variables[varnumber]))
                            if abs(coefficient)> manual_epsilon
                                    println(io,varnumber," ",blocknumber," ",i, " ",j , " ",  coefficient)
                            end
                    end
            end
        end
    end
    println("##### Writing finished.")
end

#@time MUBWriteSDPASymBlockDiagFULL(5,3,3,2)

#MUBWriteSDPA(3,3,3,3)
#@time MUBWriteSDPASymBlockDiagFULL(6,4,4,2)
