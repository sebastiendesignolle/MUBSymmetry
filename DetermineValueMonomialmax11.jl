using LinearAlgebra, GenericLinearAlgebra
using SymEngine, Combinatorics
using Printf

setprecision(128)

dictionaryMon = Dict()

@vars y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20;
@vars v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
@vars v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51
@vars v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81
@vars v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111
@vars v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141
@vars v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154
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



function bepaalwaardemonoom(d,Ivec,Kvec)
    lengtemonoom = length(Ivec);

    if (lengtemonoom == 1)
        return 1;
    end

    for index in 1:lengtemonoom    #if there is a basis which occurs only once: reduce using POVM-constraint.
        sameBasis =  findall(x -> x == Kvec[index], Kvec);
        if (length(sameBasis)==1)
            deleteat!(Kvec, sameBasis[1]);
            deleteat!(Ivec, sameBasis[1]);
            return (1/BigFloat(d))*bepaalwaardemonoom(d,Ivec,Kvec);
        end
    end


    for index1 in 1:lengtemonoom    #if there is a basis which occurs twice subsequently: reduce using Projector-constraint
        index2 = index1-1 !=0 ? index1-1 : lengtemonoom;

        if (Kvec[index1]==Kvec[index2])
            if (Ivec[index1] != Ivec[index2])
                return 0;
            else
                deleteat!(Kvec, index1);
                deleteat!(Ivec, index1);
                return bepaalwaardemonoom(d,Ivec,Kvec);
            end
        end
    end



    for index1 in 1:lengtemonoom     #If monomial contains X_{index1,k} X_{index2,l} X{index3,k}
        index2 = index1-1 !=0 ? index1-1 : lengtemonoom; #one index back
        index3 = index1-2 > 0 ? index1-2 : lengtemonoom+index1-2; #two indices back

        if (Kvec[index1]==Kvec[index3])
            if (Ivec[index1] == Ivec[index3])
                deleteat!(Kvec, index2);
                deleteat!(Ivec, index2);
                return (1/BigFloat(d))*bepaalwaardemonoom(d,Ivec,Kvec);    #if there is a monomial X_ij X_kl X_ij: reduce
            end
        end
    end



    for index1 in 1:lengtemonoom     #Reduce a monomial recursively to a monomial in which, for each of the k bases, the same basis element is chosen.
        #(So, in the reduced monomial: if the variable X_{i,k} occurs in the monomial, and the variable X_{i',k} also occurs, then i=i'.)
        basis_considered = Kvec[index1]
        indices_of_basis =  findall(x -> x == basis_considered, Kvec);

        if length(indices_of_basis) > 1
            Ivec_of_basis = [Ivec[iindex] for iindex in indices_of_basis];
            Ivec_occurring_unique=unique(Ivec_of_basis);
            Ivec_of_basis_single = []
            for i in Ivec_occurring_unique
                if count(x->x==i, Ivec_of_basis) == 1
                    Ivec_of_basis_single = push!(Ivec_of_basis_single,i)
                end
            end


            if !isempty(Ivec_of_basis_single)
                maximumI = maximum(Ivec_of_basis_single)

                if (length(Ivec_occurring_unique)>1 && Ivec[index1] == maximumI)
                    Kpart1=deepcopy(Kvec);
                    Ipart1=deepcopy(Ivec);
                    deleteat!(Kpart1,index1);
                    deleteat!(Ipart1,index1);

                    value_to_return = bepaalwaardemonoom(d,Ipart1,Kpart1);
		    #println(value_to_return)	

                    for basiselt in Ivec_occurring_unique
                        if Ivec[index1] != basiselt
                            Ivectemp=deepcopy(Ivec);
                            Kvectemp=deepcopy(Kvec);
                            Ivectemp[index1]=basiselt;
			
                            value_to_return -= bepaalwaardemonoom(d,Ivectemp, Kvectemp);

                        end
                    end
                    return value_to_return/BigFloat(d+1-length(Ivec_occurring_unique));
                end
            end
        end
    end


    Ivecnew, monoom = minimumcyclicpartIK( Ivec, Kvec );
    Kvecnew = monoom;
    ### Now we use the [XUX,XVX]=0 constraint to further reduce the variables.
    ### WORKS AT THIS POINT ONLY IF IVEC = 1,1,1,1,1 (or 0,0,0,0...,  or everywhere the same)


    if all(y->y==Ivecnew[1],Ivecnew)

        huidigvector = deepcopy(monoom);
        for index1 in 0: Int(floor(length(monoom)/2)-1)
            indices_of_basis =  findall(x -> x == index1, monoom);
            if length(indices_of_basis) > 2   #try to reduce.
                ###First we make an array A with all between-intervals, with respect to index1.
                ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
                ### array A will be [[1,2],[1,3,1],[1,2]]
                A= Any[];
                for j=1: length(indices_of_basis)-1
                    toevoegvector = monoom[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
                    push!(A,toevoegvector);
                end
                laatstetoevoegvector = [monoom[indices_of_basis[length(indices_of_basis)]+1:end], monoom[1:indices_of_basis[1]-1]]
                laatstetoevoegvector= [(laatstetoevoegvector...)...]
                push!(A,laatstetoevoegvector);



                for Ai1=1:length(A)
                    for Ai2 = 1:length(A)
                        if (Ai1 != Ai2)
                            reducevector = [index1, A[Ai1],index1,A[Ai2]]
                            for Abuildindex=1:length(A)
                                if (Abuildindex != Ai1 && Abuildindex != Ai2)
                                    push!(reducevector,index1,A[Abuildindex]);
                                end
                            end
                            reducevector=minimumcyclicpart([(reducevector...)...])
                            if ( isless(reducevector,huidigvector) )
                                huidigvector = reducevector
                            end
                            if (A[Ai1][end] == A[Ai2][1])
                                ### IN THIS CASE WE CAN REDUCE TO LOWER DIMENSION
                                return bepaalwaardemonoom(d,ones(length(monoom)),reducevector)
                            end
                        end
                    end
                end
            end
        end


        Kvecnew=huidigvector;

        if (lengtemonoom == 6 && isequal(Kvecnew, [0,1,2,0,1,2]))
            return y1;
        end


        if (lengtemonoom == 8 && isequal(Kvecnew, [0,1,2,0,3,1,2,3]))
            return  y2;
        end

        if (lengtemonoom == 8 && isequal(Kvecnew, [0,1,2,0,3,2,1,3]))
            return  y3;
        end

        if (lengtemonoom == 8 && isequal(Kvecnew, [0,1,2,3,0,1,2,3]))
            return   y4;
        end

        if (lengtemonoom == 9 && isequal(Kvecnew, [0,1,2,0,1,2,0,1,2]))
            return y5;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,1,2,3,0,1,3]))
            return y6;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,2,0,3,1,2,3]))
            return y7;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,2,3,0,1,2,3]))
            return y8;
        end

        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,1,3,4,2,3,4]))
            return v1;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,1,4,2,3,4]))
            return v2;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,1,4,3,2,4]))
            return v3;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,2,4,3,1,4]))
            return v4;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,4,1,2,3,4]))
            return v5;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,4,1,2,4,3]))
            return v6;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,4,2,1,3,4]))
            return v7;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,0,3,4,2,1,4,3]))
            return v8;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,3,0,4,1,2,3,4]))
            return v9;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,3,0,4,1,3,2,4]))
            return v10;
        end
        if (lengtemonoom == 10 && isequal(Kvecnew, [0,1,2,3,4,0,1,2,3,4]))
            return v11;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,2,3,4,0,3,4]))
            return v12;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,2,3,4,1,3,4]))
            return v13;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,0,4,2,3,4]))
            return v14;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,2,4,0,3,4]))
            return v15;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,2,4,1,3,4]))
            return v16;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,2,4,3,1,4]))
            return v17;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,4,0,3,2,4]))
            return v18;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,4,1,2,3,4]))
            return v19;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,1,3,4,1,2,4,3]))
            return v20;
        end
        if (lengtemonoom == 11 && isequal(Kvecnew, [0,1,2,0,3,1,2,4,3,1,4]))
            return v21;
        end

     
else

        beginvector  = []
        wordlength = length(monoom);
        for testindex = 1:wordlength
                push!(beginvector,(Ivecnew[testindex],monoom[testindex]))
        end

        currentelement=(deepcopy(monoom),deepcopy(Ivecnew));
        
        for consideredij in unique(beginvector)
            
            indices_of_basis =  findall(x -> x == consideredij, beginvector);
            #println(indices_of_basis)
        
            if length(indices_of_basis) > 2   #try to reduce.
                ###First we make an array A with all between-intervals, with respect to index1.
                ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
                ### array A will be [[1,2],[1,3,1],[1,2]]
                A= Any[];
                for j=1: length(indices_of_basis)-1
                    toevoegvector = beginvector[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
                    push!(A,toevoegvector);
                end
                laatstetoevoegvector = vcat(beginvector[indices_of_basis[length(indices_of_basis)]+1:end], beginvector[1:indices_of_basis[1]-1])
                push!(A,laatstetoevoegvector);

        
                for Ai1=1:length(A)
                    for Ai2 = 1:length(A)
                        if (Ai1 != Ai2)
                            reducevector = [consideredij] 
                            append!(reducevector,A[Ai1])
                            append!(reducevector,[consideredij])
                            append!(reducevector,A[Ai2])
                             for Abuildindex=1:length(A)
                                 if (Abuildindex != Ai1 && Abuildindex != Ai2)
                                     append!(reducevector,[consideredij]);
                                     append!(reducevector,A[Abuildindex]);
                                 end
                             end
                             tempI = zeros(Int,wordlength)
                             tempK = zeros(Int,wordlength)
                             for testindex = 1:wordlength
                                tempI[testindex] = reducevector[testindex][1]
                                tempK[testindex] = reducevector[testindex][2]
                             end

                             reduceI,reduceK = minimumcyclicpartIK(tempI,tempK)

        
                             if ( isless((reduceK,reduceI),currentelement) )
                                 currentelement = (deepcopy(reduceK),deepcopy(reduceI))
                             end
                             if (A[Ai1][end] == A[Ai2][1])
                                 ### IN THIS CASE WE CAN REDUCE TO LOWER DIMENSION
                                 return bepaalwaardemonoom(d,reduceI,reduceK)
                             end
                        end
                    end
                end
            end
        
        end
 
        Kvecnew=currentelement[1];
        Ivecnew=currentelement[2];

    @vars z1, z2;

    if (lengtemonoom == 8 && isequal(Ivecnew, [0,0,1,1,0,0,1,1]) && isequal(Kvecnew, [0,1,0,1,0,1,0,1]))
        return z1;
    end
    if (lengtemonoom == 8 && isequal(Ivecnew, [0,0,1,0,0,0,1,0]) && isequal(Kvecnew, [0,1,0,2,0,1,0,2]))
        return z2;
    end
	
    @vars z3, z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26;   
    	
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,0,1,2,0,1,2]))
        return z3;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,0,1,2,1,0,2]))
        return z4;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,0,2,1,0,1,2]))
        return z5;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,1,1,0,0]) && isequal(Kvecnew, [0,1,0,1,0,2,1,0,1,2]))
        return z6;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,0,1,2]))
        return z7;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,1,1,0,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,0,1,2]))
        return z8;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,1,0,0,1,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,0,1,2]))
        return z9;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,2,1,0,1,0,2]))
        return z10;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,1,0,1,1,0,0,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,0,1,2]))
        return z11;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,3,0,2,3]))
        return z12;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,1,0]) && isequal(Kvecnew, [0,1,0,2,0,1,3,2,0,3]))
        return z13;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,1,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,0,1,2,3]))
        return z14;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,1,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,0,1,3,2]))
        return z15;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,1,0,2,3]))
        return z16;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,1,0,3,2]))
        return z17;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,2,0,1,3]))
        return z18;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,3,0,2,3]))
        return z19;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,3,0,2,3]))
        return z20;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,0,2,3]))
        return z21;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,0,2,3]))
        return z22;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,0,3,2]))
        return z23;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,0,3,2]))
        return z24;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,2,0,1,3]))
        return z25;
    end
    if (lengtemonoom == 10 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,2,0,1,3]))
        return z26;
    end


    @vars z27, z28,z29,z30,z31,z32,z33,z34,z35,z36,z37,z38,z39,z40,z41,z42,z43,z44,z45,z46

    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,1,0,0,0,0,1,1,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,2,0,1,2]))
        return z27;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,1,0,0,1,0,1,0,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,2,0,1,2]))
        return z28;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,1,0,0,1,0,0,1,0]) && isequal(Kvecnew, [0,1,0,1,2,0,1,2,1,0,2]))
        return z29;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,0,2,0,1,2]))
        return z30;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,0,3,1,2,3]))
        return z31;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,1,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,0,3,2,1,3]))
        return z32;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,1,1,0,0,1]) && isequal(Kvecnew, [0,1,0,2,0,1,2,0,2,1,2]))
        return z33;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,2,3,0,2,3]))
        return z34;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,0,1,0]) && isequal(Kvecnew, [0,1,0,2,0,1,2,3,1,0,3]))
        return z35;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,1,3,0,2,1,3]))
        return z36;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,1,0,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,1,0,3,1,2]))
        return z37;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,0,3,2,1,0,3,2]))
        return z38;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,2,3,0,1,3]))
        return z39;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,2,3,0,2,3]))
        return z40;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,2,3,0,2,3]))
        return z41;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,3,1,0,2,3]))
        return z42;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,1,0,3,2,0,1,3]))
        return z43;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,2,0,1,3]))
        return z44;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,0,0,0,1,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,3,0,2,3]))
        return z45;
    end
    if (lengtemonoom == 11 && isequal(Ivecnew, [0,0,1,0,0,1,0,0,0,0,0]) && isequal(Kvecnew, [0,1,0,2,3,0,1,3,0,2,3]))
        return z46;
    end
end
end 

function bepaalwaardemonoomDict(d,Ivec,Kvec)
    if !haskey(dictionaryMon,(d,Ivec,Kvec))
        temp = bepaalwaardemonoom(d,Ivec,Kvec)
        global dictionaryMon[(d,Ivec,Kvec)] = temp
    end
    return dictionaryMon[(d,Ivec,Kvec)]
end


#NEW FASTER VERSION
function make_partition(J)  #returns lexicographically smallest element of S_n-orbit of word in {0,..,n-1}^t
    #For example: make_partition([3, 3, 2, 1]) = [0,0,1,2]
    originalJ=deepcopy(J);
    n=length(J);
    nogtehernummeren = collect(1:n) #vector of all indices

    aantalhernummerd=0;
    nieuwentry = 0;

    while aantalhernummerd < n
        kleinstetehernummeren = nogtehernummeren[1];
        gahernummeren  = findall(x -> x == originalJ[kleinstetehernummeren], originalJ);
        J[gahernummeren].= nieuwentry;

        aantalhernummerd+=length(gahernummeren)
        setdiff!(nogtehernummeren, gahernummeren);
        nieuwentry+=1;
    end

    return J
end


function  minimumcyclicpart( v )
    v=make_partition(v);
    outputvector = deepcopy(v);
    for i=1:length(v)
        vtemp = make_partition([v[i+1:end];  v[1:i]])
        if ( isless(vtemp,outputvector))
            outputvector = vtemp;
        end
    end
    return outputvector;
end

function  minimumcyclicpartIK( Ivec, Kvec )
    v=make_partition(Kvec);
    outputKvector = deepcopy(v);
    outputIvector = deepcopy(Ivec);
    for i=1:length(v)
        vtemp = make_partition([v[i+1:end];  v[1:i]])
        Itemp = [Ivec[i+1:end];  Ivec[1:i]]
        if ( isless(vtemp,outputKvector))
            outputKvector = vtemp;
            outputIvector = Itemp;
        end
    end
    return renumberIdependingOnK(outputIvector,outputKvector), outputKvector
end


function renumberIdependingOnK(Ivec,Kvec)
    for i=0:length(Kvec)/2
        PositionsToChange = findall(x->x==i, Kvec);
        Ivec[PositionsToChange] = make_partition(Ivec[PositionsToChange])
    end
    return Ivec;

end

function SmallestFromEquivalenceClass(Kvec)
    monoom = minimumcyclicpart(Kvec);
    huidigvector = deepcopy(monoom);
        for index1 in 0: Int(floor(length(monoom)/2)-1)
            indices_of_basis =  findall(x -> x == index1, monoom);
            if length(indices_of_basis) > 2   #try to reduce.
                ###First we make an array A with all between-intervals, with respect to index1.
                ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
                ### array A will be [[1,2],[1,3,1],[1,2]]
                A= Any[];
                for j=1: length(indices_of_basis)-1
                    toevoegvector = monoom[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
                    push!(A,toevoegvector);
                end
                laatstetoevoegvector = [monoom[indices_of_basis[length(indices_of_basis)]+1:end], monoom[1:indices_of_basis[1]-1]]
                laatstetoevoegvector= [(laatstetoevoegvector...)...]
                push!(A,laatstetoevoegvector);

                ##########now find the minimum lexicographic k-vector using the commutator-constraint

                for Ai1=1:length(A)
                    for Ai2 = 1:length(A)
                        if (Ai1 != Ai2)
                            ### NOW WE CAN TRY TO REDUCE. Create the reduce-vector
                            reducevector = [index1, A[Ai1],index1,A[Ai2]]
                            for Abuildindex=1:length(A)
                                if (Abuildindex != Ai1 && Abuildindex != Ai2)
                                    push!(reducevector,index1);
                                    push!(reducevector,A[Abuildindex])
                                end
                            end
                            reducevector=minimumcyclicpart([(reducevector...)...])
                            if ( isless(reducevector,huidigvector) )
                                huidigvector = reducevector
                            end
                        end

                    end
                end
            end
        end
        return huidigvector
end



function SmallestFromEquivalenceClassFull(monomialI,monomialK)  #Ivec  and Kvector 

monomialI, monomialK = minimumcyclicpartIK(monomialI,monomialK)
beginvector  = []
wordlength = length(monomialK);
for testindex = 1:wordlength
        push!(beginvector,(monomialI[testindex],monomialK[testindex]))
end
println(beginvector)
currentelement=(deepcopy(monomialK),deepcopy(monomialI));

for consideredij in unique(beginvector)
    
    indices_of_basis =  findall(x -> x == consideredij, beginvector);
    #println(indices_of_basis)

    if length(indices_of_basis) > 2   #try to reduce.
        ###First we make an array A with all between-intervals, with respect to index1.
        ###For example, if index1=0, and monoom = [0,1,2,0,1,3,1,0,1,2], then our
        ### array A will be [[1,2],[1,3,1],[1,2]]
        A= Any[];
        for j=1: length(indices_of_basis)-1
            toevoegvector = beginvector[indices_of_basis[j]+1:indices_of_basis[j+1]-1]
            push!(A,toevoegvector);
        end
        laatstetoevoegvector = vcat(beginvector[indices_of_basis[length(indices_of_basis)]+1:end], beginvector[1:indices_of_basis[1]-1])

        push!(A,laatstetoevoegvector);
        println("A: ") 
        display(A)

        for Ai1=1:length(A)
            for Ai2 = 1:length(A)
                if (Ai1 != Ai2)
                    reducevector = [consideredij] 
                    append!(reducevector,A[Ai1])
                    append!(reducevector,[consideredij])
                    append!(reducevector,A[Ai2])
                     for Abuildindex=1:length(A)
                         if (Abuildindex != Ai1 && Abuildindex != Ai2)
                             append!(reducevector,[consideredij]);
                             append!(reducevector,A[Abuildindex]);
                         end
                     end
                     tempI = zeros(Int,wordlength)
                     tempK = zeros(Int,wordlength)
                     for testindex = 1:wordlength
                        tempI[testindex] = reducevector[testindex][1]
                        tempK[testindex] = reducevector[testindex][2]
                     end

                     reduceI,reduceK = minimumcyclicpartIK(tempI,tempK)

                     if ( isless((reduceK,reduceI),currentelement) )
                         currentelement = (deepcopy(reduceK),deepcopy(reduceI))
                     end
                     if (A[Ai1][end] == A[Ai2][1])
                         ### IN THIS CASE WE CAN REDUCE TO LOWER DIMENSION
                         return bepaalwaardemonoom(d,reduceI,reduceK)
                     end
                end
            end
        end
    end
end   
 return currentelement[2], currentelement[1]   #return Ivec, Kvec.
end


function bepaalwaardemonoomTest2() 
	println("aan het werk!")
    nothingmatrix = [0 0 0 0 0 0 0 0 0 0 0]
    for k1=1,k2=2,k3=1:3,k4=1:4,k5=1:4,k6=1:4,k7=1:4,k8=1:4,k9=1:4,k10=1:4,k11=1:4,i1=1,i2=1,i3=1:2,i4=1:2,i5=1:2,i6=1:2,i7=1:2,i8=1:2,i9=1:2,i10=1:2,i11=1:2

  	I= [i1;i2;i3;i4;i5;i6;i7;i8;i9;i10;i11]
	K= [k1;k2;k3;k4;k5;k6;k7;k8;k9;k10;k11]
        if bepaalwaardemonoom(6,I,K) ===nothing
		println("I " ,I) 
		println("K " , K)
	   testI, testK = SmallestFromEquivalenceClassFull(I,K)
            println("testI: ")
            println(transpose(testI));
            println(join(testI, ','))
            println("testK: ")
            println(transpose(testK));
            println(join(testK, ','))
            nothingmatrix=[nothingmatrix; transpose(testI); transpose(testK)]
		display(nothingmatrix)
        end

    end
   # display(nothingmatrix)
    ia = unique(nothingmatrix, dims=1)
    display(ia)
end

#bepaalwaardemonoomTest2()

