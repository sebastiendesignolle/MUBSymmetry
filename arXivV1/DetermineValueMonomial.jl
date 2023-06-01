# using LinearAlgebra, GenericLinearAlgebra
# using SymEngine, Combinatorics
# using Printf
# include("ConstructReprSet.jl") #For make_partition

setprecision(128)

dictionaryMon = Dict()

function DetermineValueMonomial(d, Ivec, Kvec)
    lengtemonoom = length(Ivec)

    if (lengtemonoom == 1)
        return 1
    end

    for index in 1:lengtemonoom    #if there is a basis which occurs only once: reduce using POVM-constraint.
        sameBasis = findall(x -> x == Kvec[index], Kvec)
        if (length(sameBasis) == 1)
            deleteat!(Kvec, sameBasis[1])
            deleteat!(Ivec, sameBasis[1])
            return (1 / BigFloat(d)) * DetermineValueMonomial(d, Ivec, Kvec)
        end
    end

    for index1 in 1:lengtemonoom    #if there is a basis which occurs twice subsequently: reduce using Projector-constraint
        index2 = index1 - 1 != 0 ? index1 - 1 : lengtemonoom

        if (Kvec[index1] == Kvec[index2])
            if (Ivec[index1] != Ivec[index2])
                return 0
            else
                deleteat!(Kvec, index1)
                deleteat!(Ivec, index1)
                return DetermineValueMonomial(d, Ivec, Kvec)
            end
        end
    end

    for index1 in 1:lengtemonoom     #If monomial contains X_{index1,k} X_{index2,l} X{index1,k}
        index2 = index1 - 1 != 0 ? index1 - 1 : lengtemonoom #one index back
        index3 = index1 - 2 > 0 ? index1 - 2 : lengtemonoom + index1 - 2 #two indices back

        if (Kvec[index1] == Kvec[index3])
            if (Ivec[index1] == Ivec[index3])
                deleteat!(Kvec, index2)
                deleteat!(Ivec, index2)
                return (1 / BigFloat(d)) * DetermineValueMonomial(d, Ivec, Kvec)    #if there is a monomial X_ij X_kl X_ij: reduce
            end
        end
    end

    for index1 in 1:lengtemonoom     #Reduce a monomial using POVM-constraint 
        #applicable if one basis occurs multiple times, in which one element appears only one time
        #Used, e.g., to reduce X11*X12*X21*X22
        basis_considered = Kvec[index1]
        indices_of_basis = findall(x -> x == basis_considered, Kvec)

        if length(indices_of_basis) > 1
            Ivec_of_basis = [Ivec[iindex] for iindex in indices_of_basis]
            Ivec_occurring_unique = unique(Ivec_of_basis)
            Ivec_of_basis_single = []
            for i in Ivec_occurring_unique
                if count(x -> x == i, Ivec_of_basis) == 1
                    Ivec_of_basis_single = push!(Ivec_of_basis_single, i)
                end
            end

            if !isempty(Ivec_of_basis_single)
                maximumI = maximum(Ivec_of_basis_single)

                if (length(Ivec_occurring_unique) > 1 && Ivec[index1] == maximumI)
                    Kpart1 = deepcopy(Kvec)
                    Ipart1 = deepcopy(Ivec)
                    deleteat!(Kpart1, index1)
                    deleteat!(Ipart1, index1)

                    value_to_return = DetermineValueMonomial(d, Ipart1, Kpart1)

                    for basiselt in Ivec_occurring_unique
                        if Ivec[index1] != basiselt
                            Ivectemp = deepcopy(Ivec)
                            Kvectemp = deepcopy(Kvec)
                            Ivectemp[index1] = basiselt

                            value_to_return -= DetermineValueMonomial(d, Ivectemp, Kvectemp)
                        end
                    end
                    return value_to_return / BigFloat(d + 1 - length(Ivec_occurring_unique))
                end
            end
        end
    end

    Ivecnew, monoom = minimumcyclicpartIK(Ivec, Kvec)
    Kvecnew = monoom
    ### Now we use the [XUX,XVX]=0 constraint to further reduce the variables.
    if all(y -> y == Ivecnew[1], Ivecnew) #Check if all bases are the same
        huidigvector = deepcopy(monoom)
        for index1 in 0:Int(floor(length(monoom) / 2) - 1)
            indices_of_basis = findall(x -> x == index1, monoom)
            if length(indices_of_basis) > 2   #try to reduce.
                ###First we make an array A with all between-intervals, with respect to index1.
                ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
                ### array A will be [[1,2],[1,3,1],[1,2]]
                A = Any[]
                for j in 1:length(indices_of_basis)-1
                    toevoegvector = monoom[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
                    push!(A, toevoegvector)
                end
                laatstetoevoegvector =
                    [monoom[indices_of_basis[length(indices_of_basis)]+1:end], monoom[1:indices_of_basis[1]-1]]
                laatstetoevoegvector = [(laatstetoevoegvector...)...]
                push!(A, laatstetoevoegvector)

                for Ai1 in 1:length(A)
                    for Ai2 in 1:length(A)
                        if (Ai1 != Ai2)
                            reducevector = [index1, A[Ai1], index1, A[Ai2]]
                            for Abuildindex in 1:length(A)
                                if (Abuildindex != Ai1 && Abuildindex != Ai2)
                                    push!(reducevector, index1, A[Abuildindex])
                                end
                            end
                            reducevector = minimumcyclicpart([(reducevector...)...])
                            if (isless(reducevector, huidigvector))
                                huidigvector = reducevector
                            end
                            if (A[Ai1][end] == A[Ai2][1])
                                ### IN THIS CASE WE CAN REDUCE TO LOWER DIMENSION
                                return DetermineValueMonomial(d, ones(length(monoom)), reducevector)
                            end
                        end
                    end
                end
            end
        end

        Kvecnew = huidigvector

        if (lengtemonoom == 6 && isequal(Kvecnew, [0, 1, 2, 0, 1, 2]))
            @vars y1
            return y1
        end

        if lengtemonoom == 8
            @vars y2, y3, y4
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 3]))
                return y2
            end

            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 3]))
                return y3
            end

            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 2, 3]))
                return y4
            end
        end

        if (lengtemonoom == 9 && isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2]))
            @vars y5
            return y5
        end

        if lengtemonoom == 10
            @vars y6 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 3]))
                return y6
            end

            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 3, 4]))
                return v1
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 3, 4]))
                return v2
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 2, 4]))
                return v3
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 1, 4]))
                return v4
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 3, 4]))
                return v5
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 4, 3]))
                return v6
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 1, 3, 4]))
                return v7
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 1, 4, 3]))
                return v8
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 2, 3, 4]))
                return v9
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 3, 2, 4]))
                return v10
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 0, 1, 2, 3, 4]))
                return v11
            end
        end

        if lengtemonoom == 11
            @vars y7 y8 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 2, 3]))
                return y7
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3]))
                return y8
            end

            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 3, 4]))
                return v12
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 3, 4]))
                return v13
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 2, 3, 4]))
                return v14
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 3, 4]))
                return v15
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 1, 3, 4]))
                return v16
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 1, 4]))
                return v17
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 3, 2, 4]))
                return v18
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 2, 3, 4]))
                return v19
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 2, 4, 3]))
                return v20
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 1, 4]))
                return v21
            end
        end

        if (lengtemonoom == 12)
            @vars y9 y10 y11 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51
            @vars v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81
            @vars v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111
            @vars v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141

            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]))
                return y9
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 3, 0, 1, 3]))
                return y10
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]))
                return y11
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 0, 3, 4]))
                return v22
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 1, 3, 4]))
                return v23
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 2, 3, 4]))
                return v24
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 1, 3, 4]))
                return v25
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 2, 3, 4]))
                return v26
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 3, 1, 4]))
                return v27
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 3, 2, 4]))
                return v28
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 0, 3, 4]))
                return v29
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 2, 3, 4]))
                return v30
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 3, 1, 4]))
                return v31
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 3, 2, 4]))
                return v32
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 3, 4]))
                return v33
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 4, 3]))
                return v34
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 3, 1, 4]))
                return v35
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 3, 2, 4]))
                return v36
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 2, 3, 4]))
                return v37
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 2, 4, 3]))
                return v38
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 3, 2, 4]))
                return v39
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 0, 3, 4]))
                return v40
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 0, 4, 3]))
                return v41
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 3, 1, 4]))
                return v42
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 4, 5]))
                return v43
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 1, 4, 2, 3, 4]))
                return v44
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 1, 2, 3, 4]))
                return v45
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 2, 4, 3, 1, 4]))
                return v46
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 2, 1, 3, 4]))
                return v47
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 1, 3, 4]))
                return v48
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 3, 1, 4]))
                return v49
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 3, 2, 4]))
                return v50
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 1, 3, 4]))
                return v51
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 1, 4, 3]))
                return v52
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 3, 1, 4]))
                return v53
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 3, 2, 4]))
                return v54
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 1, 2, 4, 3]))
                return v55
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 1, 3, 2, 4]))
                return v56
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 4, 5]))
                return v57
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 4, 5]))
                return v58
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 3, 5]))
                return v59
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 4, 5]))
                return v60
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 5, 4]))
                return v61
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 3, 5]))
                return v62
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 5, 3]))
                return v63
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 2, 4, 5]))
                return v64
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 2, 5, 4]))
                return v65
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 3, 4, 1, 2, 4]))
                return v66
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 3, 1, 4]))
                return v67
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 1, 2, 4]))
                return v68
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 4, 5]))
                return v69
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 4, 3, 5]))
                return v70
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 5, 2, 4, 5]))
                return v71
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 5, 4, 2, 5]))
                return v72
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 4, 5]))
                return v73
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 5, 4]))
                return v74
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 4, 3, 5]))
                return v75
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 2, 4, 5]))
                return v76
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 2, 5, 4]))
                return v77
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 4, 2, 5]))
                return v78
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 3, 4, 5]))
                return v79
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 4, 3, 5]))
                return v80
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 5, 4, 1, 5]))
                return v81
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 3, 4, 5]))
                return v82
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 3, 5, 4]))
                return v83
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 3, 1, 4, 5]))
                return v84
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 3, 1, 5, 4]))
                return v85
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 3, 4, 5]))
                return v86
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 4, 3, 5]))
                return v87
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 3, 5, 2, 4, 5]))
                return v88
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 2, 3, 4, 5]))
                return v89
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 2, 3, 5, 4]))
                return v90
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 2, 4, 3, 5]))
                return v91
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 2, 4, 5, 3]))
                return v92
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 3, 2, 4, 5]))
                return v93
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 3, 2, 5, 4]))
                return v94
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 3, 4, 2, 5]))
                return v95
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 4, 2, 3, 5]))
                return v96
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 4, 3, 2, 5]))
                return v97
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 1, 5, 3, 4, 5]))
                return v98
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 1, 5, 4, 3, 5]))
                return v99
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 1, 3, 4, 5]))
                return v100
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 1, 4, 3, 5]))
                return v101
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 3, 1, 4, 5]))
                return v102
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 3, 1, 5, 4]))
                return v103
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 3, 4, 5]))
                return v104
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 3, 5, 4]))
                return v105
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 4, 3, 5]))
                return v106
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 4, 5, 3]))
                return v107
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 5, 3, 4]))
                return v108
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 2, 5, 4, 3]))
                return v109
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 3, 2, 4, 5]))
                return v110
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 3, 2, 5, 4]))
                return v111
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 3, 4, 2, 5]))
                return v112
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 1, 3, 5, 2, 4]))
                return v113
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 3, 4, 5]))
                return v114
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 3, 5, 4]))
                return v115
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 4, 3, 5]))
                return v116
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 4, 5, 3]))
                return v117
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 5, 3, 4]))
                return v118
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 1, 5, 4, 3]))
                return v119
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 3, 1, 4, 5]))
                return v120
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 5, 2, 3, 1, 5, 4]))
                return v121
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 4, 5, 2, 3, 4, 5]))
                return v122
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 4, 5, 3, 2, 4, 5]))
                return v123
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 5, 2, 3, 4, 5]))
                return v124
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 5, 2, 4, 3, 5]))
                return v125
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 5, 3, 2, 4, 5]))
                return v126
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 1, 5, 3, 4, 2, 5]))
                return v127
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 1, 2, 3, 4, 5]))
                return v128
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 1, 2, 3, 5, 4]))
                return v129
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 1, 3, 2, 4, 5]))
                return v130
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 1, 3, 2, 5, 4]))
                return v131
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 2, 1, 3, 4, 5]))
                return v132
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 2, 1, 3, 5, 4]))
                return v133
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 2, 3, 1, 4, 5]))
                return v134
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 2, 3, 1, 5, 4]))
                return v135
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 4, 5, 3, 2, 1, 5, 4]))
                return v136
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 0, 5, 1, 2, 3, 4, 5]))
                return v137
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 0, 5, 1, 2, 4, 3, 5]))
                return v138
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 0, 5, 1, 3, 2, 4, 5]))
                return v139
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 0, 5, 2, 1, 4, 3, 5]))
                return v140
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]))
                return v141
            end
        end

        if (lengtemonoom == 13)
            @vars y12 y13 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154
            @vars v155 v156 v157 v158 v159 v160 v161 v162 v163 v164 v165 v166 v167 v168 v169 v170 v171 v172 v173 v174 v175 v176 v177 v178 v179 v180 v181 v182 v183 v184
            @vars v185 v186 v187 v188 v189 v190 v191 v192 v193 v194 v195 v196 v197 v198 v199 v200 v201 v202 v203 v204 v205 v206 v207 v208 v209 v210 v211 v212 v213 v214
            @vars v215 v216 v217 v218 v219 v220 v221 v222 v223 v224 v225 v226 v227 v228 v229 v230 v231 v232 v233 v234 v235 v236 v237 v238 v239 v240 v241 v242 v243 v244
            @vars v245 v246 v247 v248 v249 v250 v251 v252 v253 v254 v255 v256 v257 v258 v259 v260 v261 v262 v263 v264 v265 v266 v267 v268 v269 v270 v271 v272 v273 v274
            @vars v275 v276 v277 v278 v279 v280 v281 v282 v283 v284 v285 v286 v287 v288 v289 v290 v291 v292 v293 v294 v295 v296 v297 v298 v299 v300 v301 v302 v303 v304
            @vars v305 v306 v307 v308 v309 v310 v311 v312 v313 v314 v315 v316 v317 v318 v319 v320 v321 v322 v323 v324 v325 v326 v327 v328 v329 v330 v331 v332 v333 v334
            @vars v335 v336 v337 v338 v339 v340 v341 v342 v343 v344 v345 v346 v347 v348 v349 v350 v351 v352 v353 v354 v355 v356 v357 v358 v359 v360 v361 v362 v363 v364
            @vars v365 v366 v367 v368 v369 v370 v371 v372 v373 v374 v375 v376 v377 v378 v379 v380 v381 v382 v383 v384 v385 v386 v387 v388 v389 v390 v391 v392 v393 v394
            @vars v395 v396 v397 v398 v399 v400 v401 v402 v403 v404 v405 v406 v407 v408 v409 v410 v411 v412 v413 v414 v415 v416 v417 v418 v419 v420 v421 v422 v423 v424
            @vars v425 v426 v427 v428 v429 v430 v431 v432 v433 v434 v435 v436 v437 v438 v439 v440 v441 v442 v443 v444 v445 v446 v447 v448 v449 v450 v451 v452 v453 v454

            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 0, 1, 3]))
                return y12
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 1, 2, 3]))
                return y13
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 3, 4, 0, 3, 4]))
                return v142
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 3, 4, 1, 3, 4]))
                return v143
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 3, 4, 2, 3, 4]))
                return v144
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 4, 0, 3, 4]))
                return v145
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 4, 2, 3, 4]))
                return v146
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 4, 3, 1, 4]))
                return v147
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 4, 3, 2, 4]))
                return v148
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 2, 4, 0, 3, 4]))
                return v149
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 2, 4, 1, 3, 4]))
                return v150
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 2, 4, 3, 1, 4]))
                return v151
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 2, 4, 3, 2, 4]))
                return v152
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 1, 2, 3, 4]))
                return v153
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 1, 2, 4, 3]))
                return v154
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 1, 3, 2, 4]))
                return v155
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 2, 3, 1, 4]))
                return v156
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 4, 5, 3, 4, 5]))
                return v157
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 4, 2, 3, 4]))
                return v158
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 4, 3, 1, 4]))
                return v159
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 4, 3, 2, 4]))
                return v160
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 1, 2, 3, 4]))
                return v161
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 1, 2, 4, 3]))
                return v162
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 1, 3, 2, 4]))
                return v163
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 2, 3, 1, 4]))
                return v164
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 3, 1, 2, 4]))
                return v165
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 3, 1, 4, 3]))
                return v166
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 4, 5, 3, 4, 5]))
                return v167
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 2, 4, 0, 3, 4]))
                return v168
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 2, 4, 3, 1, 4]))
                return v169
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 0, 3, 2, 4]))
                return v170
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 2, 0, 3, 4]))
                return v171
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 2, 0, 4, 3]))
                return v172
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 5, 3, 4, 5]))
                return v173
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4]))
                return v174
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 2, 4, 3]))
                return v175
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 3, 2, 4]))
                return v176
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 1, 4, 2, 3]))
                return v177
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 3, 1, 2, 4]))
                return v178
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 5, 3, 4, 5]))
                return v179
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 0, 5, 4, 3, 5]))
                return v180
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 2, 0, 3, 4]))
                return v181
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 2, 0, 4, 3]))
                return v182
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 1, 4, 3, 0, 4, 3]))
                return v183
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 5, 3, 4, 5]))
                return v184
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 5, 4, 3, 5]))
                return v185
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 0, 3, 1, 4]))
                return v186
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 0, 4, 1, 3]))
                return v187
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 3, 0, 1, 4]))
                return v188
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 5, 3, 4, 5]))
                return v189
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 2, 5, 4, 3, 5]))
                return v190
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 0, 3, 4, 5]))
                return v191
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 0, 3, 5, 4]))
                return v192
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 0, 4, 3, 5]))
                return v193
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 0, 4, 5, 3]))
                return v194
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 1, 3, 4, 5]))
                return v195
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 1, 3, 5, 4]))
                return v196
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 1, 4, 3, 5]))
                return v197
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 1, 4, 5, 3]))
                return v198
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 2, 3, 4, 5]))
                return v199
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 2, 3, 5, 4]))
                return v200
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 2, 4, 3, 5]))
                return v201
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 2, 4, 5, 3]))
                return v202
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 0, 4, 5]))
                return v203
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 0, 5, 4]))
                return v204
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 1, 4, 5]))
                return v205
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 1, 5, 4]))
                return v206
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 2, 4, 5]))
                return v207
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 2, 5, 4]))
                return v208
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 4, 1, 5]))
                return v209
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 5, 3, 4, 2, 5]))
                return v210
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 2, 5, 3, 4, 5]))
                return v211
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 2, 5, 4, 3, 5]))
                return v212
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 5, 2, 3, 4, 5]))
                return v213
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 5, 2, 3, 5, 4]))
                return v214
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 5, 2, 4, 3, 5]))
                return v215
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 3, 4, 1, 2, 4]))
                return v216
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 3, 4, 1, 3, 4]))
                return v217
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 1, 3, 2, 4]))
                return v218
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 1, 2, 3, 4]))
                return v219
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 5, 3, 4, 5]))
                return v220
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 1, 3, 2, 4]))
                return v221
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 5, 3, 4, 5]))
                return v222
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 0, 5, 4, 3, 5]))
                return v223
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 4, 2, 3, 4, 1, 3]))
                return v224
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 1, 5, 3, 4, 5]))
                return v225
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 1, 5, 4, 3, 5]))
                return v226
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 1, 4, 3, 2, 4, 3]))
                return v227
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 5, 0, 4, 5]))
                return v228
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 5, 1, 4, 5]))
                return v229
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 5, 2, 4, 5]))
                return v230
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 5, 4, 1, 5]))
                return v231
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 3, 5, 4, 2, 5]))
                return v232
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 0, 3, 4, 5]))
                return v233
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 0, 3, 5, 4]))
                return v234
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 0, 4, 3, 5]))
                return v235
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 0, 4, 5, 3]))
                return v236
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 1, 3, 4, 5]))
                return v237
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 1, 3, 5, 4]))
                return v238
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 1, 4, 3, 5]))
                return v239
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 1, 4, 5, 3]))
                return v240
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 0, 4, 5]))
                return v241
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 0, 5, 4]))
                return v242
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 1, 4, 5]))
                return v243
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 1, 5, 4]))
                return v244
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 2, 4, 5]))
                return v245
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 2, 5, 4]))
                return v246
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 4, 1, 5]))
                return v247
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 5, 3, 4, 2, 5]))
                return v248
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 0, 1, 2, 4, 3, 2, 4]))
                return v249
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 0, 4, 3, 2, 4, 3]))
                return v250
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 3, 5, 2, 4, 5]))
                return v251
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 3, 5, 4, 2, 5]))
                return v252
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 2, 3, 4, 5]))
                return v253
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 2, 3, 5, 4]))
                return v254
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 2, 4, 3, 5]))
                return v255
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 2, 4, 5, 3]))
                return v256
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 3, 2, 4, 5]))
                return v257
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 3, 2, 5, 4]))
                return v258
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 3, 4, 2, 5]))
                return v259
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 4, 2, 3, 5]))
                return v260
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 4, 2, 5, 3]))
                return v261
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 5, 4, 3, 2, 5]))
                return v262
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 2, 5, 3, 4, 5]))
                return v263
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 2, 5, 4, 3, 5]))
                return v264
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 3, 5, 2, 4, 5]))
                return v265
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 2, 3, 4, 5]))
                return v266
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 2, 3, 5, 4]))
                return v267
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 2, 4, 3, 5]))
                return v268
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 2, 4, 5, 3]))
                return v269
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 3, 2, 4, 5]))
                return v270
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 3, 2, 5, 4]))
                return v271
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 3, 4, 2, 5]))
                return v272
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 4, 2, 3, 5]))
                return v273
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 4, 2, 5, 3]))
                return v274
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 5, 4, 3, 2, 5]))
                return v275
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 0, 5, 3, 4, 5]))
                return v276
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 0, 5, 4, 3, 5]))
                return v277
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 4, 1, 3, 4, 2, 3]))
                return v278
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 3, 5, 1, 4, 5]))
                return v279
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 3, 5, 4, 1, 5]))
                return v280
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 3, 5, 4, 2, 5]))
                return v281
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 0, 3, 4, 5]))
                return v282
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 0, 3, 5, 4]))
                return v283
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 0, 4, 3, 5]))
                return v284
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 0, 4, 5, 3]))
                return v285
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 1, 3, 4, 5]))
                return v286
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 1, 3, 5, 4]))
                return v287
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 1, 4, 3, 5]))
                return v288
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 1, 4, 5, 3]))
                return v289
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 0, 4, 5]))
                return v290
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 0, 5, 4]))
                return v291
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 1, 4, 5]))
                return v292
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 1, 5, 4]))
                return v293
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 2, 5, 4]))
                return v294
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 4, 1, 5]))
                return v295
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 3, 4, 2, 5]))
                return v296
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 0, 3, 5]))
                return v297
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 0, 5, 3]))
                return v298
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 1, 3, 5]))
                return v299
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 1, 5, 3]))
                return v300
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 3, 1, 5]))
                return v301
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 2, 5, 4, 3, 2, 5]))
                return v302
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 3, 2, 4, 5]))
                return v303
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 3, 2, 5, 4]))
                return v304
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 3, 4, 2, 5]))
                return v305
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 3, 5, 2, 4]))
                return v306
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 4, 2, 3, 5]))
                return v307
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 4, 2, 5, 3]))
                return v308
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 0, 4, 3, 2, 5]))
                return v309
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 3, 4, 5]))
                return v310
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 3, 5, 4]))
                return v311
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 4, 3, 5]))
                return v312
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 4, 5, 3]))
                return v313
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 5, 3, 4]))
                return v314
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 2, 5, 4, 3]))
                return v315
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 3, 2, 4, 5]))
                return v316
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 3, 2, 5, 4]))
                return v317
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 3, 4, 2, 5]))
                return v318
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 3, 5, 2, 4]))
                return v319
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 4, 2, 3, 5]))
                return v320
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 4, 2, 5, 3]))
                return v321
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 4, 3, 2, 5]))
                return v322
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 1, 4, 5, 2, 3]))
                return v323
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 0, 4, 5]))
                return v324
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 0, 5, 4]))
                return v325
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 1, 4, 5]))
                return v326
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 3, 1, 5, 4]))
                return v327
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 0, 3, 5]))
                return v328
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 0, 5, 3]))
                return v329
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 1, 3, 5]))
                return v330
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 2, 4, 1, 5, 3]))
                return v331
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 0, 4, 2, 5]))
                return v332
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 0, 5, 2, 4]))
                return v333
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 1, 4, 2, 5]))
                return v334
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 5, 3, 1, 5, 2, 4]))
                return v335
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 3, 0, 4, 1, 2, 4]))
                return v336
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 1, 2, 4, 0, 3, 4]))
                return v337
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 3, 1, 2, 4]))
                return v338
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 5, 3, 4, 5]))
                return v339
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 5, 4, 3, 5]))
                return v340
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 1, 2, 4, 3]))
                return v341
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 1, 4, 2, 3]))
                return v342
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 5, 1, 4, 5]))
                return v343
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 5, 2, 4, 5]))
                return v344
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 5, 4, 1, 5]))
                return v345
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 3, 5, 4, 2, 5]))
                return v346
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 0, 3, 4, 5]))
                return v347
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 0, 3, 5, 4]))
                return v348
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 0, 4, 3, 5]))
                return v349
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 1, 4, 3, 5]))
                return v350
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 2, 3, 5, 4]))
                return v351
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 0, 4, 5]))
                return v352
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 0, 5, 4]))
                return v353
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 1, 4, 5]))
                return v354
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 1, 5, 4]))
                return v355
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 2, 4, 5]))
                return v356
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 2, 5, 4]))
                return v357
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 4, 1, 5]))
                return v358
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 5, 3, 4, 2, 5]))
                return v359
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 2, 4, 1, 3, 2, 4, 3]))
                return v360
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 3, 5, 2, 4, 5]))
                return v361
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 3, 5, 4, 2, 5]))
                return v362
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 2, 3, 4, 5]))
                return v363
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 2, 3, 5, 4]))
                return v364
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 2, 4, 3, 5]))
                return v365
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 3, 2, 4, 5]))
                return v366
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 3, 2, 5, 4]))
                return v367
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 3, 4, 2, 5]))
                return v368
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 4, 2, 3, 5]))
                return v369
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 0, 5, 4, 3, 2, 5]))
                return v370
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 2, 4, 0, 1, 3, 2, 4]))
                return v371
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 3, 5, 1, 4, 5]))
                return v372
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 3, 5, 4, 1, 5]))
                return v373
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 3, 5, 4, 2, 5]))
                return v374
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 0, 3, 4, 5]))
                return v375
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 0, 3, 5, 4]))
                return v376
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 0, 4, 3, 5]))
                return v377
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 1, 4, 3, 5]))
                return v378
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 1, 4, 5, 3]))
                return v379
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 0, 4, 5]))
                return v380
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 0, 5, 4]))
                return v381
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 1, 4, 5]))
                return v382
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 1, 5, 4]))
                return v383
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 4, 1, 5]))
                return v384
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 3, 4, 2, 5]))
                return v385
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 4, 1, 5, 3]))
                return v386
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 2, 5, 4, 3, 1, 5]))
                return v387
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 0, 5, 2, 4, 5]))
                return v388
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 0, 5, 4, 2, 5]))
                return v389
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 2, 5, 1, 4, 5]))
                return v390
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 2, 5, 4, 1, 5]))
                return v391
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 5, 0, 4, 2, 5]))
                return v392
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 5, 2, 4, 1, 5]))
                return v393
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 3, 5, 4, 1, 2, 5]))
                return v394
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 3, 2, 4, 5]))
                return v395
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 3, 2, 5, 4]))
                return v396
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 3, 4, 2, 5]))
                return v397
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 3, 5, 2, 4]))
                return v398
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 4, 2, 3, 5]))
                return v399
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 0, 4, 3, 2, 5]))
                return v400
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 1, 2, 3, 4, 5]))
                return v401
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 1, 2, 3, 5, 4]))
                return v402
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 1, 2, 5, 3, 4]))
                return v403
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 1, 2, 5, 4, 3]))
                return v404
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 0, 4, 5]))
                return v405
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 0, 5, 4]))
                return v406
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 4, 1, 5]))
                return v407
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 2, 3, 5, 4, 3]))
                return v408
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 0, 5, 2, 4]))
                return v409
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 1, 2, 4, 5]))
                return v410
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 1, 2, 5, 4]))
                return v411
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 1, 4, 2, 5]))
                return v412
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 1, 5, 2, 4]))
                return v413
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 2, 4, 5, 3]))
                return v414
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 1, 4, 5, 3, 4, 1, 2, 5]))
                return v415
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 3, 4, 0, 2, 4, 1, 3, 4]))
                return v416
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 0, 5, 4, 3, 5]))
                return v417
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 3, 5, 4, 1, 5]))
                return v418
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 5, 0, 3, 4, 5]))
                return v419
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 5, 3, 0, 4, 5]))
                return v420
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 5, 3, 0, 5, 4]))
                return v421
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 5, 3, 1, 4, 5]))
                return v422
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 1, 4, 5, 3, 1, 5, 4]))
                return v423
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 3, 5, 2, 4, 5]))
                return v424
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 0, 3, 4, 5]))
                return v425
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 0, 4, 3, 5]))
                return v426
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 3, 0, 4, 5]))
                return v427
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 1, 5, 3, 0, 5, 4]))
                return v428
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 1, 5, 2, 4, 5]))
                return v429
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 5, 1, 2, 4, 5]))
                return v430
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 5, 1, 2, 5, 4]))
                return v431
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 3, 5, 1, 4, 5, 3]))
                return v432
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 2, 4, 5, 3]))
                return v433
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 2, 5, 4, 3]))
                return v434
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 3, 0, 4, 5]))
                return v435
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 1, 3, 0, 5, 4]))
                return v436
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 3, 1, 2, 4, 5]))
                return v437
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 2, 4, 5, 3, 1, 2, 5, 4]))
                return v438
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 3, 4, 1, 2, 3]))
                return v439
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 3, 5, 4, 2, 5]))
                return v440
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 4, 5, 3, 2, 5]))
                return v441
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 0, 3, 4, 5]))
                return v442
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 0, 4, 3, 5]))
                return v443
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 3, 4, 2, 5]))
                return v444
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 4, 1, 3, 5]))
                return v445
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 4, 1, 5, 3]))
                return v446
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 2, 5, 4, 3, 2, 5]))
                return v447
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 3, 4, 1, 2, 5]))
                return v448
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 1, 5, 3, 4, 2, 5, 3]))
                return v449
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 3, 1, 4, 2, 5]))
                return v450
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 3, 4, 2, 5, 3, 4, 1, 2, 5]))
                return v451
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 1, 2, 4]))
                return v452
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 4, 3, 5, 0, 4, 2, 5]))
                return v453
            end
            if (isequal(Kvecnew, [0, 1, 2, 3, 0, 1, 4, 3, 5, 1, 2, 4, 5]))
                return v454
            end
        end
        if lengtemonoom == 14
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 3, 1, 2, 3]))
                return y14
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3]))
                return y15
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 3, 1, 2, 3, 1, 2, 3]))
                return y16
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 3]))
                return y17
            end
        end
        if lengtemonoom == 15
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]))
                return y18
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 3, 0, 1, 3]))
                return y19
            end
            if (isequal(Kvecnew, [0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]))
                return y20
            end
        end
    else
        beginvector = []
        wordlength = length(monoom)
        for testindex in 1:wordlength
            push!(beginvector, (Ivecnew[testindex], monoom[testindex]))
        end

        currentelement = (deepcopy(monoom), deepcopy(Ivecnew))

        for consideredij in unique(beginvector)
            indices_of_basis = findall(x -> x == consideredij, beginvector)
            #println(indices_of_basis)

            if length(indices_of_basis) > 2   #try to reduce.
                ###First we make an array A with all between-intervals, with respect to index1.
                ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
                ### array A will be [[1,2],[1,3,1],[1,2]]
                A = Any[]
                for j in 1:length(indices_of_basis)-1
                    toevoegvector = beginvector[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
                    push!(A, toevoegvector)
                end
                laatstetoevoegvector =
                    vcat(beginvector[indices_of_basis[length(indices_of_basis)]+1:end], beginvector[1:indices_of_basis[1]-1])
                push!(A, laatstetoevoegvector)

                for Ai1 in 1:length(A)
                    for Ai2 in 1:length(A)
                        if (Ai1 != Ai2)
                            reducevector = [consideredij]
                            append!(reducevector, A[Ai1])
                            append!(reducevector, [consideredij])
                            append!(reducevector, A[Ai2])
                            for Abuildindex in 1:length(A)
                                if (Abuildindex != Ai1 && Abuildindex != Ai2)
                                    append!(reducevector, [consideredij])
                                    append!(reducevector, A[Abuildindex])
                                end
                            end
                            tempI = zeros(Int, wordlength)
                            tempK = zeros(Int, wordlength)
                            for testindex in 1:wordlength
                                tempI[testindex] = reducevector[testindex][1]
                                tempK[testindex] = reducevector[testindex][2]
                            end

                            reduceI, reduceK = minimumcyclicpartIK(tempI, tempK)

                            if (isless((reduceK, reduceI), currentelement))
                                currentelement = (deepcopy(reduceK), deepcopy(reduceI))
                            end
                            if (A[Ai1][end] == A[Ai2][1])
                                ### IN THIS CASE WE CAN REDUCE TO LOWER DIMENSION
                                return DetermineValueMonomial(d, reduceI, reduceK)
                            end
                        end
                    end
                end
            end
        end

        Kvecnew = currentelement[1]
        Ivecnew = currentelement[2]

        if lengtemonoom == 8
            @vars z1, z2
            if isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 1, 1]) && isequal(Kvecnew, [0, 1, 0, 1, 0, 1, 0, 1])
                return z1
            end
            if isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 0, 2])
                return z2
            end
        end

        if lengtemonoom == 10
            @vars z3,
            z4,
            z5,
            z6,
            z7,
            z8,
            z9,
            z10,
            z11,
            z12,
            z13,
            z14,
            z15,
            z16,
            z17,
            z18,
            z19,
            z20,
            z21,
            z22,
            z23,
            z24,
            z25,
            z26

            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 0, 1, 2, 0, 1, 2]))
                return z3
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 0, 1, 2, 1, 0, 2]))
                return z4
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 0, 2, 1, 0, 1, 2]))
                return z5
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 1, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 0, 2, 1, 0, 1, 2]))
                return z6
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 0, 1, 2]))
                return z7
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 1, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 0, 1, 2]))
                return z8
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 1, 0, 0, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 0, 1, 2]))
                return z9
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 1, 0, 1, 0, 2]))
                return z10
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 1, 1, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 0, 1, 2]))
                return z11
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 3, 0, 2, 3]))
                return z12
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 3, 2, 0, 3]))
                return z13
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 0, 1, 2, 3]))
                return z14
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 0, 1, 3, 2]))
                return z15
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 1, 0, 2, 3]))
                return z16
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 1, 0, 3, 2]))
                return z17
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 2, 0, 1, 3]))
                return z18
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 3, 0, 2, 3]))
                return z19
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 3, 0, 2, 3]))
                return z20
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 0, 2, 3]))
                return z21
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 0, 2, 3]))
                return z22
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 0, 3, 2]))
                return z23
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 0, 3, 2]))
                return z24
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 2, 0, 1, 3]))
                return z25
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 2, 0, 1, 3]))
                return z26
            end
        end

        if lengtemonoom == 11
            @vars z27, z28, z29, z30, z31, z32, z33, z34, z35, z36, z37, z38, z39, z40, z41, z42, z43, z44, z45, z46
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2]))
                return z27
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2]))
                return z28
            end
            if (isequal(Ivecnew, [0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 1, 2, 0, 1, 2, 1, 0, 2]))
                return z29
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 2]))
                return z30
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 0, 3, 1, 2, 3]))
                return z31
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 0, 3, 2, 1, 3]))
                return z32
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2]))
                return z33
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 2, 3, 0, 2, 3]))
                return z34
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 2, 3, 1, 0, 3]))
                return z35
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 1, 3, 0, 2, 1, 3]))
                return z36
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 1, 0, 3, 1, 2]))
                return z37
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 0, 3, 2, 1, 0, 3, 2]))
                return z38
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 2, 3, 0, 1, 3]))
                return z39
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 2, 3, 0, 2, 3]))
                return z40
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 2, 3, 0, 2, 3]))
                return z41
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 3, 1, 0, 2, 3]))
                return z42
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 1, 0, 3, 2, 0, 1, 3]))
                return z43
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 2, 0, 1, 3]))
                return z44
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 3, 0, 2, 3]))
                return z45
            end
            if (isequal(Ivecnew, [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0]) && isequal(Kvecnew, [0, 1, 0, 2, 3, 0, 1, 3, 0, 2, 3]))
                return z46
            end
        end
    end
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
        vtemp = make_partition([v[i+1:end]; v[1:i]])
        Itemp = [Ivec[i+1:end]; Ivec[1:i]]
        if (isless(vtemp, outputKvector))
            outputKvector = vtemp
            outputIvector = Itemp
        end
    end
    return renumberIdependingOnK(outputIvector, outputKvector), outputKvector
end

function renumberIdependingOnK(Ivec, Kvec)
    for i in 0:length(Kvec)/2
        PositionsToChange = findall(x -> x == i, Kvec)
        Ivec[PositionsToChange] = make_partition(Ivec[PositionsToChange])
    end
    return Ivec
end
