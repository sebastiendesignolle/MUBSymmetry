function DetValMon(VarSet, DictValueMon, d, Ivec, Kvec, coeff)

    #Initialize
    NewVar = false

    #Reduce to the coset representative (lexicographically smallest element)
    Ivecnew, Kvecnew = minimumLexico(Ivec, Kvec)

    #If this monomial has previously been declared a variable...
    if (Ivec, Kvec) in VarSet
        DictValueMon[(Ivec, Kvec)] = 1 * coeff
        return NewVar, DictValueMon
    end

    #If the length of the monomial is 1, then its trace is 1
    lengthMonomial = length(Ivec)
    if (lengthMonomial == 1)
        DictValueMon[([-1], [-1])] = haskey(DictValueMon, ([-1], [-1])) ? DictValueMon[([-1], [-1])] + 1 * coeff : 1 * coeff
        return NewVar, DictValueMon
    end

    #If there is a basis which occurs twice subsequently: reduce using Projector/orthogonality-constraint
    for index1 in 1:lengthMonomial
        index2 = index1 - 1 != 0 ? index1 - 1 : lengthMonomial
        if (Kvec[index1] == Kvec[index2])
            if (Ivec[index1] != Ivec[index2])
                DictValueMon[([-1], [-1])] = haskey(DictValueMon, ([-1], [-1])) ? DictValueMon[([-1], [-1])] : 0
                return NewVar, DictValueMon
            else
                deleteat!(Kvec, index1)
                deleteat!(Ivec, index1)
                return DetValMon(VarSet, DictValueMon, d, Ivec, Kvec, coeff)
            end
        end
    end

    #If there is a basis which occurs only once: reduce using POVM-constraint.
    for index in 1:lengthMonomial
        sameBasis = findall(x -> x == Kvec[index], Kvec)
        if (length(sameBasis) == 1)
            deleteat!(Kvec, sameBasis[1])
            deleteat!(Ivec, sameBasis[1])
            return DetValMon(VarSet, DictValueMon, d, Ivec, Kvec, coeff * (1 / Rational{Int}(d)))
        end
    end

    #Reduce a monomial recursively using POVM-constraint if there exists a basis in which one basis element occurs once
    for index1 in 1:lengthMonomial
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

                    #Identity:
                    NewVar, DictValueMon = DetValMon(
                        VarSet,
                        DictValueMon,
                        d,
                        Ipart1,
                        Kpart1,
                        coeff * (1 / Rational{Int}(d + 1 - length(Ivec_occurring_unique))),
                    )
                    #Minus the others:
                    for basiselt in Ivec_occurring_unique
                        TempDictionary = Dict{Tuple{Vector{Int}, Vector{Int}}, Rational{Int}}()
                        if Ivec[index1] != basiselt
                            Ivectemp = deepcopy(Ivec)
                            Kvectemp = deepcopy(Kvec)
                            Ivectemp[index1] = basiselt
                            # value_to_return -= DetermineValueMonomial(d,Ivectemp, Kvectemp);
                            VarSet, TempDictionary = DetValMon(
                                VarSet,
                                TempDictionary,
                                d,
                                Ivectemp,
                                Kvectemp,
                                -coeff * (1 / Rational{Int}(d + 1 - length(Ivec_occurring_unique))),
                            )
                            DictValueMon = merge(+, DictValueMon, TempDictionary)
                        end
                    end
                    # return value_to_return/Rational{Int}(d+1-length(Ivec_occurring_unique));
                    # return VarSet,DictValueMon = DetValMon(VarSet,DictValueMon,d,Ivec,Kvec,coeff/Rational{Int}(d+1-length(Ivec_occurring_unique)); #I have modified the coefficient above instead
                    return NewVar, DictValueMon
                end
            end
        end
    end

    #If monomial contains X_{index1,k} X_{index2,l} X{index1,k} for k neq l
    for index1 in 1:lengthMonomial
        index2 = index1 - 1 != 0 ? index1 - 1 : lengthMonomial #one index back
        index3 = index1 - 2 > 0 ? index1 - 2 : lengthMonomial + index1 - 2 #two indices back
        if (Kvec[index1] == Kvec[index3])
            if (Ivec[index1] == Ivec[index3])
                deleteat!(Kvec, index2)
                deleteat!(Ivec, index2)
                return DetValMon(VarSet, DictValueMon, d, Ivec, Kvec, coeff * (1 / Rational{Int}(d)))    #Replace X_ij X_kl X_ij by 1/d*X_ij
            end
        end
    end

    ##Now use commutator constraints to find the coset for which the coset representative is smallest
    Currentelement = (deepcopy(Kvecnew), deepcopy(Ivecnew))
    CurrentMonomial = []
    wordlength = length(Kvecnew)
    for testindex in 1:wordlength
        push!(CurrentMonomial, (Ivecnew[testindex], Kvecnew[testindex]))
    end
    for consideredij in unique(CurrentMonomial) #Candidate 'outer variable'
        indices_of_elementij = findall(x -> x == consideredij, CurrentMonomial)
        if length(indices_of_elementij) > 2   #try to reduce.
            ###First we make an array A with all between-intervals, with respect to index1.
            ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
            ### array A will be [[1,2],[1,3,1],[1,2]]
            A = Any[]
            for j in 1:length(indices_of_elementij)-1
                intermediateblock = CurrentMonomial[indices_of_elementij[j]+1:indices_of_elementij[j+1]-1]
                push!(A, intermediateblock)
            end
            lastintermediateblock = vcat(
                CurrentMonomial[indices_of_elementij[length(indices_of_elementij)]+1:end],
                CurrentMonomial[1:indices_of_elementij[1]-1],
            )
            push!(A, lastintermediateblock)

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

                        reduceI, reduceK = minimumLexico(tempI, tempK)
                        if (isless((reduceK, reduceI), Currentelement))
                            Currentelement = (deepcopy(reduceK), deepcopy(reduceI))
                        end

                        if (A[Ai1][end] == A[Ai2][1]) ### IN THIS CASE WE CAN REDUCE TO LOWER DEGREE via the degree-3 MUB constraint
                            return DetValMon(VarSet, DictValueMon, d, reduceI, reduceK, coeff)
                        end
                    end
                end
            end
        end
    end
    Ivecnew = Currentelement[2]
    Kvecnew = Currentelement[1]

    #We cannot reduce further: we add the monomial to the list of variables and assign it weight 1*coeff for the value dictionary
    DictValueMon[(Ivecnew, Kvecnew)] = 1 * coeff
    NewVar = true
    return NewVar, DictValueMon
end
