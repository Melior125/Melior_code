#include <vector>
#include "Sumcheck.cpp"
#include <mcl/bn256.hpp>
#include <iostream>
#include <stdexcept>
#include "pcs.hpp" 
using namespace std;
using namespace mcl::bn;

std::vector<Fr> foldDimsSeparate(
    const std::vector<Fr>& table,
    unsigned int n,
    unsigned int m,
    const std::vector<Fr>& rAll
) {
    size_t totalSize = table.size(); // = 2^(n+m)
    // std::cout<<totalSize<<" "<<(1u<<(n+m))<<std::endl;
    if (totalSize != (1u << (n+m))) {
        throw std::runtime_error("[foldDimsSeparate] size mismatch");
    }
    if (rAll.size() != n) {
        throw std::runtime_error("[foldDimsSeparate] rAll dimension mismatch");
    }

    std::vector<Fr> T = table;
    size_t sizeT = totalSize;

    for (unsigned int i=0; i<n; i++){
        Fr rVal=rAll[i];
        size_t halfSize = sizeT / 2;
        for (size_t j=0; j<halfSize; j++){
            auto t0 = T[2*j];
            auto t1 = T[2*j +1];
            auto diff = t1 - t0;
            T[j]      = t0 + diff * rVal;
        }
        sizeT = halfSize;
    }

    if(sizeT != (1u << m)) {
        throw std::runtime_error("[foldDimsSeparate] final size != 2^m?");
    }

    std::vector<Fr> res(sizeT);
    for (size_t i=0; i<sizeT; i++){
        res[i] = T[i];
    }
    return res;
}


std::vector<Fr> get_random_shift_column(
    const std::vector<Fr>& A2D,  // size= 2^(nVars + kVars)
    unsigned int nVars,  // row bits
    unsigned int kVars,  // col bits
    const std::vector<Fr>& r1  // length= nVars
){

    return foldDimsSeparate(A2D, nVars, kVars, r1);
}


std::vector<Fr> foldLastDimsSeparate(
    const std::vector<Fr>& table,
    unsigned int n,  // 保留的维度bit数(前 n 位)
    unsigned int m,  // 要折叠(固定)的后 m 位
    const std::vector<Fr>& rAll  // 长度=m
) {
    // 这个函数是用来计算A[r1,k]这样的bkp table的，但是在大字端编码下，是A[k||r1]
    // 所以input应该是n = 列数，m=行数
    // 这个函数的逻辑就是大字端，他在合并c++这种矩阵存储方式的行
    size_t totalSize = table.size(); // = 2^(n+m)
    if (totalSize != (1u << (n+m))) {
        throw std::runtime_error("[foldLastDimsSeparate] size mismatch");
    }
    if (rAll.size() != m) {
        throw std::runtime_error("[foldLastDimsSeparate] rAll dimension mismatch");
    }

    std::vector<Fr> transposed(totalSize);

    for(size_t idx=0; idx<totalSize; idx++){
        // row = lower n bits, col = higher m bits
        size_t row = idx & ((1u<<n)-1);  // row \in [0..2^n-1]
        size_t col = idx >> n;          // col \in [0..2^m-1]
        // newIdx = col + (row << m)
        size_t newIdx = col + (row << m);
        transposed[newIdx] = table[idx];
    }


    auto folded = foldDimsSeparate(transposed, m, n, rAll);
    return folded;
}

std::vector<Fr> get_random_shift_row(
    const std::vector<Fr>& B2D,
    unsigned int kVars,  // row bits
    unsigned int mVars,  // col bits
    const std::vector<Fr>& r2 // length=mVars
) {
    return foldLastDimsSeparate(B2D, kVars, mVars, r2);
}

std::tuple<bool, Fr,Fr,Fr,Fr,Fr,std::vector<Fr>> Designed_Int_Sumcheck_for_Rational_MatrixMul(const std::vector<Fr>& f, const std::vector<Fr>& g, const std::vector<Fr>& h, const std::vector<Fr>& gg, const std::vector<Fr>& hh,
    const Fr& ClaimedValue, const unsigned& kVars, const Fr& lambda, const Fr& lambda2){

    Fr Claimed_Sum = ClaimedValue;
    // std::cout<<Claimed_Sum<<std::endl;
    // P computes 4 points and sends them to V
    int max_degree = 3;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(kVars,Fr(0));
    std::vector<Fr> Sumcheck_f = f;
    std::vector<Fr> Sumcheck_g = g;
    std::vector<Fr> Sumcheck_h = h;
    std::vector<Fr> Sumcheck_gg = gg;
    std::vector<Fr> Sumcheck_hh = hh;
    for(unsigned int i=0; i<kVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_f(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_g(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_h(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_gg(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_hh(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_f[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, Fr(j));
            Auxiliary_h[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_h, Fr(j));
            Auxiliary_g[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, Fr(j));
            Auxiliary_hh[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_hh, Fr(j));
            Auxiliary_gg[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_gg, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_f[0][kk] = Sumcheck_f[kk*2];
            Auxiliary_f[1][kk] = Sumcheck_f[kk*2+1];
            Auxiliary_h[0][kk] = Sumcheck_h[kk*2];
            Auxiliary_h[1][kk] = Sumcheck_h[kk*2+1];
            Auxiliary_g[0][kk] = Sumcheck_g[kk*2];
            Auxiliary_g[1][kk] = Sumcheck_g[kk*2+1];
            Auxiliary_hh[0][kk] = Sumcheck_hh[kk*2];
            Auxiliary_hh[1][kk] = Sumcheck_hh[kk*2+1];
            Auxiliary_gg[0][kk] = Sumcheck_gg[kk*2];
            Auxiliary_gg[1][kk] = Sumcheck_gg[kk*2+1];
            // std::cout<<Auxiliary_hh[0][kk] * Auxiliary_gg[0][kk]<<" "<<Auxiliary_hh[1][kk] * Auxiliary_gg[1][kk]<<std::endl;
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_f[j][jj] * (lambda * Auxiliary_g[j][jj]* Auxiliary_hh[j][jj] + Auxiliary_gg[j][jj]* Auxiliary_h[j][jj]) + 
                lambda2 * Auxiliary_f[j][jj] * (Auxiliary_gg[j][jj]* Auxiliary_hh[j][jj]-Fr(1));
                // std::cout<<lambda2 * Auxiliary_f[j][jj] * (Auxiliary_gg[j][jj]* Auxiliary_hh[j][jj]-Fr(1))<<" "<<(Auxiliary_gg[j][jj]* Auxiliary_hh[j][jj]-Fr(1))<<std::endl;
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) {
            std::cout<<"Designed failed in round "<<i<<std::endl;
            break;
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_f = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, r_i);
        Sumcheck_g = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, r_i);
        Sumcheck_h = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_h, r_i);
        Sumcheck_gg = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_gg, r_i);
        Sumcheck_hh = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_hh, r_i);
    }
    if (!ok) {
        std::cout<<"Designed Sumcheck failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), Fr(0), Fr(0), Fr(0), Fr(0), r_Challenges);
    }
    ok == ((Sumcheck_f[0]*(lambda * Sumcheck_g[0]*Sumcheck_hh[0] + Sumcheck_gg[0]*Sumcheck_h[0]) + lambda2 * Sumcheck_f[0] * (Sumcheck_gg[0]*Sumcheck_hh[0]-1)) == Claimed_Sum);
    return std::make_tuple(ok, Sumcheck_f[0], Sumcheck_g[0], Sumcheck_h[0], Sumcheck_gg[0], Sumcheck_hh[0], r_Challenges);
}

std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> Rational_MatrixMul (
    std::vector<Fr> A_num, std::vector<Fr> A_den,
    std::vector<Fr> B_num, std::vector<Fr> B_den,
    std::vector<Fr> C_num, std::vector<Fr> C_den,
    unsigned int mVars,
    unsigned int nVars,
    unsigned int kVars,
    // std::vector<Fr> r, const Rational_Fr& claimC_r,
    G1&G,G1*g
){
    // timer t;
    bool ok=false;
    std::vector<Fr> AA(1u<<(mVars+nVars),Fr(0));
    std::vector<Fr> BB(1u<<(nVars + kVars),Fr(0));
    std::vector<Fr> CC(1u<<(mVars + kVars),Fr(0));
    std::vector<Fr> rChallenges(1u<<nVars,Fr(0));
    for (unsigned int i=0;i<(1u<<(mVars+nVars));i++){
        AA[i] = A_num[i] / A_den[i];
    }
    for (unsigned int i=0;i<(1u<<(kVars+nVars));i++){
        BB[i] = B_num[i] / B_den[i];
    }
    for (unsigned int i=0;i<(1u<<(kVars+mVars));i++){
        CC[i] = C_num[i] / C_den[i];
    }
    std::vector<Fr> r1(mVars,Fr(0));
    std::vector<Fr> r2(kVars,Fr(0));
    std::vector<Fr> rCC(mVars+kVars,Fr(0));
    for (unsigned int i=0;i<kVars;i++){
        Fr r_i;r_i.setRand();
        r2[i] = r_i;
        rCC[i] = r_i;
    }
    for (unsigned int i=0;i<mVars;i++){
        Fr r_i;r_i.setRand();
        r1[i] = r_i;
        rCC[kVars+i] = r_i;
    }
    Fr claimedCC = Int_Multi_evaluate(CC,rCC,mVars+kVars);
    // P commit AA and BB and E and F
    G1* Commit_AA = prover_commit_Fr(AA.data(),g,mVars+nVars,16);
    G1* Commit_BB = prover_commit_Fr(BB.data(),g,nVars+kVars,16);
    G1* Commit_CC = prover_commit_Fr(CC.data(),g,mVars+kVars,16);
    openCommit(CC,rCC.data(),claimedCC,G,g,Commit_CC,mVars+kVars);

    std::vector<Fr> AA_r1_k(1u<<nVars);
    AA_r1_k = get_random_shift_row(AA, nVars, mVars, r1);   // A(r1, k)
    std::vector<Fr> BB_k_r2(1u<<nVars);
    BB_k_r2 = get_random_shift_column(BB, kVars, nVars, r2);   // B(k, r2)
    // std::cout<<"AA_r1_j and BB_j_r2 ok"<< std::endl;
    // P and V runs a Int_sumcheck_fx_gx to prove AA*BB=CC
    std::tuple<bool,Fr,Fr,std::vector<Fr>> ok1 = Int_Sumcheck_fx_gx(AA_r1_k,BB_k_r2,claimedCC,nVars);
    if (!std::get<0>(ok1)){
        std::cout<<"AA*BB=CC failed"<<std::endl;
        return std::make_tuple(false, Fr(0), rChallenges,Fr(0),rChallenges,Fr(0),rChallenges,Fr(0), rChallenges,Fr(0), rChallenges,Fr(0),rChallenges);
    }
    std::vector<Fr> rAA(mVars+nVars,Fr(0)), rBB(nVars+kVars,Fr(0));
    for (unsigned i=0;i<nVars;i++){
        rAA[i] = std::get<3>(ok1)[i];
    }
    for (unsigned i=0;i<mVars;i++){
        rAA[nVars+i] = r1[i];
    }
    for (unsigned i=0;i<kVars;i++){
        rBB[i] = r2[i];
    }
    for (unsigned i=0;i<nVars;i++){
        rBB[kVars+i] = std::get<3>(ok1)[i];
    }
    openCommit(AA,rAA.data(),std::get<1>(ok1),G,g,Commit_AA,mVars+nVars);
    openCommit(BB,rBB.data(),std::get<2>(ok1),G,g,Commit_BB,nVars+kVars);
    
    Fr ClaimedA_num = Int_Multi_evaluate(A_num,rAA,mVars+nVars);
    Fr ClaimedB_num = Int_Multi_evaluate(B_num,rBB,kVars+nVars);
    Fr ClaimedC_num = Int_Multi_evaluate(C_num,rCC,kVars+mVars);
    // cout<<"compute Anum Bnum Cnum"<<endl;
    vector<Fr> eqA = computeEqA(nVars+mVars,rAA);
    vector<Fr> eqB = computeEqA(nVars+kVars,rBB);
    vector<Fr> eqC = computeEqA(kVars+mVars,rCC);
    timer t;


    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> okA = Int_Sumcheck_fx_gx_hx(eqA,A_den,AA,ClaimedA_num,mVars+nVars);
    if (!std::get<0>(okA)){
        std::cout<<"Rational MatrixMul failed because AA failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), rChallenges,Fr(0),rChallenges, Fr(0),rChallenges,Fr(0),rChallenges,Fr(0),rChallenges,Fr(0), rChallenges);
    }
    openCommit(AA,std::get<4>(okA).data(),std::get<3>(okA),G,g,Commit_AA,mVars+nVars);




    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> okB = Int_Sumcheck_fx_gx_hx(eqB,B_den,BB,ClaimedB_num,kVars+nVars);
    if (!std::get<0>(okB)){
        std::cout<<"Rational MatrixMul failed because BB failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), rChallenges,Fr(0),rChallenges, Fr(0),rChallenges,Fr(0),rChallenges,Fr(0),rChallenges,Fr(0), rChallenges);
    }
    openCommit(BB,std::get<4>(okB).data(),std::get<3>(okB),G,g,Commit_BB,kVars+nVars);



    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> okC = Int_Sumcheck_fx_gx_hx(eqC,C_den,CC,ClaimedC_num,mVars+kVars);
    if (!std::get<0>(okC)){
        std::cout<<"Rational MatrixMul failed because CC failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), rChallenges,Fr(0),rChallenges, Fr(0),rChallenges,Fr(0),rChallenges,Fr(0),rChallenges,Fr(0), rChallenges);
    }
    openCommit(CC,std::get<4>(okC).data(),std::get<3>(okC),G,g,Commit_CC,mVars+kVars);

    return std::make_tuple(true, ClaimedA_num, rAA, std::get<2>(okA), std::get<4>(okA), ClaimedB_num, rBB, std::get<2>(okB), std::get<4>(okB), ClaimedC_num, rCC,std::get<2>(okC),std::get<4>(okC));
}


Fr eqClassic(const std::vector<int>& i, const std::vector<Fr>& r) {
    if (i.size() != r.size()) {
        throw std::runtime_error("Dimension mismatch in eqClassic");
    }
    std::size_t m = r.size();
    Fr val;
    val = Fr(1);
    
    for (std::size_t j = 0; j < m; j++) {
        Fr term1 = r[j] * Fr(i[j]);         // e_i * x_i
        Fr term2 = (Fr(1) - r[j]) * Fr(1 - i[j]); // (1 - e_i) * (1 - x_i)
        val *= (term1 + term2);
    }
    return val;
}

std::vector<Fr> eqTable(const std::vector<Fr>& r, const unsigned& n){
    std::vector<Fr> T(1u<<n);
    for (std::size_t idx=0; idx<(1u<<n);idx++){
        T[idx] = eqClassic(indexToBits(idx, n),r);
    }
    return T;
}

bool Int_Hadamard_A_B_C(const std::vector<std::vector<Fr>>& A, const std::vector<std::vector<Fr>>& B, const std::vector<std::vector<Fr>>& C, 
    // ll*A_int, ll*B_int, ll*C_int, 
    const unsigned& mVars, const unsigned& nVars,
    G1* commitA, G1* commitB, G1* commitC,G1&G,G1*g){
        // not done
        // ll A_Int[1<<(mVars+nVars)], B_Int[1<<(mVars+nVars)], C_Int[1<<(mVars+nVars)];
        std::vector<Fr> r1(mVars,Fr(0)), r2(nVars,Fr(0)), r(mVars+nVars,Fr(0));
        for (unsigned int i=0;i<mVars;i++){
            Fr r_i;r_i.setRand();
            r1[i] = r_i;
            r[nVars+i] = r_i;
        }
        for (unsigned int i=0;i<nVars;i++){
            Fr r_i;r_i.setRand();
            r2[i] = r_i;
            r[i] = r_i;
        }
        std::vector<Fr> eq_r = eqTable(r,mVars+nVars);
        Fr sum1 = Fr(0), sum2 = Fr(0);
        std::vector<Fr> A_vector((1u<<(mVars+nVars)),Fr(0)), B_vector((1u<<(mVars+nVars)),Fr(0)), C_vector((1u<<(mVars+nVars)),Fr(0));
        for (unsigned i=0;i<(1<<mVars);i++){
            for (unsigned j=0;j<(1<<nVars);j++){
                sum1 = sum1 + eq_r[i*(1u<<nVars)+j] * A[i][j] * B[i][j];
                A_vector[i*(1u<<nVars)+j] = A[i][j];
                B_vector[i*(1u<<nVars)+j] = B[i][j];
            }
        }
        for (unsigned i=0;i<(1<<mVars);i++){
            for (unsigned j=0;j<(1<<nVars);j++){
                sum2 = sum2 + eq_r[i*(1u<<nVars)+j] * C[i][j];
                C_vector[i*(1u<<nVars)+j] = C[i][j];
            }
        }
        if (sum1 == sum2) std::cout<<"yes you've understood index and encoding"<<std::endl;
        bool ok=false;
        std::tuple<bool, Fr, Fr, std::vector<Fr>> ok1;
        std::tuple<bool, Fr, Fr, Fr, std::vector<Fr>> ok2;
        ok1 = Int_Sumcheck_fx_gx(eq_r,C_vector,sum2,mVars+nVars);
        ok2 = Int_Sumcheck_fx_gx_hx(eq_r,A_vector,B_vector,sum1,mVars+nVars);
        ok = (std::get<0>(ok1) && std::get<0>(ok2));
        std::cout<<"last check before pcs open: "<<ok<<std::endl;

        openCommit(C_vector, std::get<3>(ok1).data(), std::get<2>(ok1), G, g, commitC, static_cast<int>(mVars+nVars));
        return ok;
}

std::tuple<bool, Fr, Fr,Fr,Fr,Fr,Fr, std::vector<Fr>> Rational_Hadamard_A_B_C(const std::vector<Fr>& A1,const std::vector<Fr>& A2, const std::vector<Fr>& B1,const std::vector<Fr>& B2, 
    const std::vector<Fr>& C1,const std::vector<Fr>& C2, 
    // ll*A_int, ll*B_int, ll*C_int, 
    const unsigned& mVars, const unsigned& nVars,
    G1&G,G1*g){
    // ll A_Int[1<<(mVars+nVars)], B_Int[1<<(mVars+nVars)], C_Int[1<<(mVars+nVars)];
    std::vector<Fr> r = RandomFieldChallenge_Generator(mVars+nVars);
    std::vector<Fr> eq_r = eqTable(r,mVars+nVars);
    Fr sum1 = Fr(0), sum2 = Fr(0);
    std::vector<Fr> A1_vector((1u<<(mVars+nVars)),Fr(0)),A2_vector((1u<<(mVars+nVars)),Fr(0)), B1_vector((1u<<(mVars+nVars)),Fr(0)),B2_vector((1u<<(mVars+nVars)),Fr(0)),
        C1_vector((1u<<(mVars+nVars)),Fr(0)),C2_vector((1u<<(mVars+nVars)),Fr(0));
    A1_vector = A1;
    A2_vector = A2;
    B1_vector = B1;
    B2_vector = B2;
    C1_vector = C1;
    C2_vector = C2;

    std::tuple<bool, Fr, Fr,Fr,Fr,Fr,Fr,Fr, std::vector<Fr>> ok = Designed_Int_Sumcheck_for_Rational_Hadamard_fghw(A1_vector,A2_vector,B1_vector,B2_vector,C1_vector,C2_vector,eq_r,Fr(0),mVars+nVars);
    if (!std::get<0>(ok)){
        std::cout<<"degree 4 sumcheck failed"<<std::endl;
        return std::make_tuple(false,Fr(0),Fr(0),Fr(0),Fr(0),Fr(0),Fr(0),std::get<8>(ok));
    }
    return std::make_tuple(true,std::get<1>(ok),std::get<2>(ok),std::get<3>(ok),std::get<4>(ok),std::get<5>(ok),std::get<6>(ok),std::get<8>(ok));
}

std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> Rational_Hadamard_A_B(const std::vector<Fr>& A1,const std::vector<Fr>& A2, const std::vector<Fr>& B1,const std::vector<Fr>& B2, 
    const Fr& C1,const Fr& C2, const vector<Fr>& r,
    const unsigned& mVars,
    G1&G,G1*g){
    std::vector<Fr> eq_r = computeEqA(mVars,r);

    Fr lambda;lambda.setRand();
    Fr Claimed_Sum = C1+lambda*C2;
    int max_degree = 3;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(mVars,Fr(0));
    std::vector<Fr> Sumcheck_eq = eq_r;
    std::vector<Fr> Sumcheck_a1 = A1;
    std::vector<Fr> Sumcheck_a2 = A2;
    std::vector<Fr> Sumcheck_b1 = B1;
    std::vector<Fr> Sumcheck_b2 = B2;
    int kVars = mVars;
    for(unsigned int i=0; i<mVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(1)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_a1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, Fr(j));
            Auxiliary_a2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, Fr(j));
            Auxiliary_b1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, Fr(j));
            Auxiliary_b2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_a1[0][kk] = Sumcheck_a1[kk*2];
            Auxiliary_a1[1][kk] = Sumcheck_a1[kk*2+1];
            Auxiliary_a2[0][kk] = Sumcheck_a2[kk*2];
            Auxiliary_a2[1][kk] = Sumcheck_a2[kk*2+1];
            Auxiliary_b1[0][kk] = Sumcheck_b1[kk*2];
            Auxiliary_b1[1][kk] = Sumcheck_b1[kk*2+1];
            Auxiliary_b2[0][kk] = Sumcheck_b2[kk*2];
            Auxiliary_b2[1][kk] = Sumcheck_b2[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_a1[j][jj]* Auxiliary_b1[j][jj] + lambda * Auxiliary_a2[j][jj]* Auxiliary_b2[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) {
            std::cout<<"Rational Hadamard protocol failed"<<std::endl;
            break;
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
        Sumcheck_a1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, r_i);
        Sumcheck_a2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, r_i);
        Sumcheck_b1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, r_i);
        Sumcheck_b2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, r_i);
    }
    if (!ok){
        std::cout<<"Rational Hadamard protocol failed"<<std::endl;
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    ok == (Sumcheck_eq[0]*(Sumcheck_a1[0]*Sumcheck_b1[0] + lambda * Sumcheck_a2[0]*Sumcheck_b2[0]) == Claimed_Sum);
    if (!ok){
        std::cout<<"Rational Hadamard protocol last round failed"<<std::endl;
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    return std::make_tuple(ok, Sumcheck_a1[0], Sumcheck_a2[0], Sumcheck_b1[0],Sumcheck_b2[0], r_Challenges);
}


std::vector<Fr> flatten_2d(const std::vector<std::vector<Fr>>& mat) {
    std::vector<Fr> flat;
    flat.reserve(mat.size() * (mat.empty() ? 0 : mat[0].size())); // 预分配空间

    for (const auto& row : mat) {
        flat.insert(flat.end(), row.begin(), row.end());
    }

    return flat;
}


std::tuple<bool, Fr, std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>> Rational_Dot_Hadamard (
    // std::vector<Rational_Fr> Matrix_A,
    // std::vector<Rational_Fr> Matrix_B,
    // std::vector<Rational_Fr> Matrix_C,
    const std::vector<Fr>& A_num,
    const std::vector<Fr>& A_den,
    const std::vector<Fr>& B_num,
    const std::vector<Fr>& B_den,
    const std::vector<Fr>& C_num,
    const std::vector<Fr>& C_den,
    unsigned int mVars,
    unsigned int nVars,
    // std::vector<Fr> r, const Rational_Fr& claimC_r,
    G1&G,G1*g
){
    // std::vector<Fr> A_num(1u<<(mVars+nVars),Fr(0));
    // std::vector<Fr> A_den(1u<<(mVars+nVars),Fr(0));
    std::vector<Fr> AA(1u<<(mVars+nVars),Fr(0));
    // std::vector<Fr> B_num(1u<<(nVars + mVars),Fr(0));
    // std::vector<Fr> B_den(1u<<(nVars + mVars),Fr(0));
    std::vector<Fr> BB(1u<<(nVars + mVars),Fr(0));
    // std::vector<Fr> C_num(1u<<(mVars),Fr(0));
    // std::vector<Fr> C_den(1u<<(mVars),Fr(0));
    std::vector<Fr> CC(1u<<(mVars),Fr(0));
    // V generates random fields to test AA*BB =CC
    std::vector<Fr> r1(1u<<mVars,Fr(0));
    for (unsigned int i=0;i<mVars;i++){
        Fr r_i;r_i.setRand();
        r1[i] = r_i;
    }
    for (unsigned int i=0;i<(1u<<(mVars+nVars));i++){
        // A_num[i] = Matrix_A[i].numerator;
        // A_den[i] = Matrix_A[i].denominator;
        AA[i] = A_num[i] / A_den[i];
    }
    for (unsigned int i=0;i<(1u<<(mVars+nVars));i++){
        // B_num[i] = Matrix_B[i].numerator;
        // B_den[i] = Matrix_B[i].denominator;
        BB[i] = B_num[i] / B_den[i];
    }
    for (unsigned int i=0;i<(1u<<(mVars));i++){
        // C_num[i] = Matrix_C[i].numerator;
        // C_den[i] = Matrix_C[i].denominator;
        CC[i] = C_num[i] / C_den[i];
    }
    // P commit AA and BB and E and F
    G1* Commit_AA = prover_commit_Fr(AA.data(),g,mVars+nVars,16);
    G1* Commit_BB = prover_commit_Fr(BB.data(),g,nVars+mVars,16);
    G1* Commit_CC = prover_commit_Fr(CC.data(),g,mVars,16);

    Fr claimCC = Int_Multi_evaluate(CC,r1,mVars);
    openCommit(CC,r1.data(),claimCC,G,g,Commit_CC,mVars);
    std::vector<Fr> eq0 = computeEqA(mVars,r1);

    std::vector<Fr> eq2(1u<<(mVars+nVars), Fr(1));
    for (unsigned int i=0;i<(1u<<mVars);i++){
        for (unsigned int j=0;j<(1u<<nVars);j++){
            eq2[i*(1u<<nVars)+j] = eq0[i];
        }
    }
    std::tuple<bool, Fr,Fr,Fr, std::vector<Fr>> ok0 = Int_Sumcheck_fx_gx_hx(eq2,AA,BB,claimCC,mVars+nVars);
    if (!std::get<0>(ok0)){
        cout<<"AA*BB!=CC"<<endl;
        return std::make_tuple(false, Fr(0), r1,Fr(0),r1,Fr(0), r1,Fr(0),r1, Fr(0), r1,Fr(0),r1);
    }
    openCommit(AA,std::get<4>(ok0).data(),std::get<2>(ok0),G,g,Commit_AA,mVars+nVars);
    openCommit(BB,std::get<4>(ok0).data(),std::get<3>(ok0),G,g,Commit_BB,mVars+nVars);

    // V then generates two random point rA and rB to prove the AA and BB and CC correctness
    // P computes the value of A_num at rA and B_num at rB. P and V further runs the sumcheck to prove AA and BB are computed correctly
    Fr Claimed_A_num,Claimed_B_num;
    std::vector<Fr> rA(mVars+nVars,Fr(0)), rB(mVars+nVars,Fr(0)), rC(mVars,Fr(0));
    for (unsigned i=0;i<(mVars+nVars);i++){
        rA[i].setRand();
    }
    for (unsigned i=0;i<(mVars+nVars);i++){
        rB[i].setRand();
    }
    for (unsigned i=0;i<mVars;i++){
        rC[i].setRand();
    }
    Claimed_A_num = Int_Multi_evaluate(A_num,rA,mVars+nVars);
    Claimed_B_num = Int_Multi_evaluate(B_num,rB,mVars+nVars);

    std::vector<Fr> eqA = computeEqA(mVars+nVars,rA);
    std::vector<Fr> eqB = computeEqA(mVars+nVars,rB);

    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> ok2 = Int_Sumcheck_fx_gx_hx(eqA,AA,A_den,Claimed_A_num,mVars+nVars);
    if (!std::get<0>(ok2)){
        std::cout<<"AA failed"<<std::endl;
        return std::make_tuple(false, Fr(0), r1,Fr(0),r1,Fr(0), r1,Fr(0),r1, Fr(0), r1,Fr(0),r1);
    }
    openCommit(AA,std::get<4>(ok2).data(),std::get<2>(ok2),G,g,Commit_AA,mVars+nVars);

    // P and V runs sumcheck for BB
    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> ok3 = Int_Sumcheck_fx_gx_hx(eqB,BB,B_den,Claimed_B_num,mVars+nVars);
    if (!std::get<0>(ok3)){
        std::cout<<"BB failed"<<std::endl;
        return std::make_tuple(false, Fr(0), r1,Fr(0),r1,Fr(0), r1,Fr(0),r1, Fr(0), r1,Fr(0),r1);
    }
    openCommit(BB,std::get<4>(ok3).data(),std::get<2>(ok3),G,g,Commit_BB,mVars+nVars);
    // then proves C2[r]*CC[r] = C1[r]
    std::vector<Fr> eqC = computeEqA(mVars,rC);

    Fr claimC_num = Int_Multi_evaluate(C_num,rC,mVars);
    // Fr claimC_den = claimC_r.denominator;
    std::tuple<bool,Fr,Fr,Fr,std::vector<Fr>> ok4 = Int_Sumcheck_fx_gx_hx(eqC,CC,C_den,claimC_num,mVars);
    if (!std::get<0>(ok4)){
        std::cout<<"CC failed"<<std::endl;
        return std::make_tuple(false, Fr(0), r1,Fr(0),r1,Fr(0), r1,Fr(0),r1, Fr(0), r1,Fr(0),r1);
    }
    openCommit(CC,std::get<4>(ok4).data(),std::get<2>(ok4),G,g,Commit_CC,mVars);

    return std::make_tuple(true, Claimed_A_num, rA, std::get<3>(ok2), std::get<4>(ok2), Claimed_B_num, rB, std::get<3>(ok3), std::get<4>(ok3), claimC_num,rC,std::get<3>(ok4),std::get<4>(ok4));
}

std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>> Rational_Addition(const std::vector<Fr>& A1,const std::vector<Fr>& A2, const std::vector<Fr>& B1,const std::vector<Fr>& B2, 
    const Fr& C1,const Fr& C2, const vector<Fr>& r,
    // ll*A_int, ll*B_int, ll*C_int, 
    const unsigned& mVars,
    G1&G,G1*g){
    // ll A_Int[1<<(mVars+nVars)], B_Int[1<<(mVars+nVars)], C_Int[1<<(mVars+nVars)];
    std::vector<Fr> eq_r = computeEqA(mVars,r);
    Fr lambda;lambda.setRand();
    Fr Claimed_Sum = C1 + lambda*C2;
    int max_degree = 3;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(mVars,Fr(0));
    std::vector<Fr> Sumcheck_eq = eq_r;
    std::vector<Fr> Sumcheck_a1 = A1;
    std::vector<Fr> Sumcheck_a2 = A2;
    std::vector<Fr> Sumcheck_b1 = B1;
    std::vector<Fr> Sumcheck_b2 = B2;
    int kVars = mVars;
    for(unsigned int i=0; i<mVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(1)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_a1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, Fr(j));
            Auxiliary_a2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, Fr(j));
            Auxiliary_b1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, Fr(j));
            Auxiliary_b2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_a1[0][kk] = Sumcheck_a1[kk*2];
            Auxiliary_a1[1][kk] = Sumcheck_a1[kk*2+1];
            Auxiliary_a2[0][kk] = Sumcheck_a2[kk*2];
            Auxiliary_a2[1][kk] = Sumcheck_a2[kk*2+1];
            Auxiliary_b1[0][kk] = Sumcheck_b1[kk*2];
            Auxiliary_b1[1][kk] = Sumcheck_b1[kk*2+1];
            Auxiliary_b2[0][kk] = Sumcheck_b2[kk*2];
            Auxiliary_b2[1][kk] = Sumcheck_b2[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_a1[j][jj]* Auxiliary_b2[j][jj] + Auxiliary_a2[j][jj]* Auxiliary_b1[j][jj] + lambda * Auxiliary_a2[j][jj] * Auxiliary_b2[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) {
            std::cout<<"addition protocol failed"<<std::endl;
            break;
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
        Sumcheck_a1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, r_i);
        Sumcheck_a2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, r_i);
        Sumcheck_b1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, r_i);
        Sumcheck_b2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, r_i);
    }
    if (!ok){
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    ok == (Sumcheck_eq[0]*(Sumcheck_a1[0]*Sumcheck_b2[0] + Sumcheck_a2[0]*Sumcheck_b1[0] + lambda *Sumcheck_a2[0]*Sumcheck_b2[0] ) == Claimed_Sum);
    if (!ok){
        std::cout<<"addition protocol failed"<<std::endl;
        std::cout<<"addition protocol last round failed"<<std::endl;
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    return std::make_tuple(ok, Sumcheck_a1[0], Sumcheck_a2[0], Sumcheck_b1[0],Sumcheck_b2[0], r_Challenges);
}


std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>> Rational_Equal(const std::vector<Fr>& A1,const std::vector<Fr>& A2, const std::vector<Fr>& B1,const std::vector<Fr>& B2, 
    // ll*A_int, ll*B_int, ll*C_int, 
    const unsigned& mVars,
    G1&G,G1*g){
    std::vector<Fr> r(mVars,Fr(0));
    for (unsigned int i=0;i<mVars;i++){
        Fr r_i;r_i.setRand();
        r[i]=r_i;
    }
    std::vector<Fr> eq_r = computeEqA(mVars,r);
    Fr Claimed_Sum = Fr(0);
    int max_degree = 3;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(mVars,Fr(0));
    std::vector<Fr> Sumcheck_eq = eq_r;
    std::vector<Fr> Sumcheck_a1 = A1;
    std::vector<Fr> Sumcheck_a2 = A2;
    std::vector<Fr> Sumcheck_b1 = B1;
    std::vector<Fr> Sumcheck_b2 = B2;
    int kVars = mVars;
    for(unsigned int i=0; i<mVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(1)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_a1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, Fr(j));
            Auxiliary_a2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, Fr(j));
            Auxiliary_b1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, Fr(j));
            Auxiliary_b2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_a1[0][kk] = Sumcheck_a1[kk*2];
            Auxiliary_a1[1][kk] = Sumcheck_a1[kk*2+1];
            Auxiliary_a2[0][kk] = Sumcheck_a2[kk*2];
            Auxiliary_a2[1][kk] = Sumcheck_a2[kk*2+1];
            Auxiliary_b1[0][kk] = Sumcheck_b1[kk*2];
            Auxiliary_b1[1][kk] = Sumcheck_b1[kk*2+1];
            Auxiliary_b2[0][kk] = Sumcheck_b2[kk*2];
            Auxiliary_b2[1][kk] = Sumcheck_b2[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_a1[j][jj]* Auxiliary_b2[j][jj] - Auxiliary_a2[j][jj]* Auxiliary_b1[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) {
            std::cout<<"Equal protocol failed"<<std::endl;
            break;
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
        Sumcheck_a1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, r_i);
        Sumcheck_a2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, r_i);
        Sumcheck_b1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, r_i);
        Sumcheck_b2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, r_i);
    }
    if (!ok){
        std::cout<<"Equal protocol failed"<<std::endl;
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    ok == (Sumcheck_eq[0]*(Sumcheck_a1[0]*Sumcheck_b2[0] - Sumcheck_a2[0]*Sumcheck_b1[0]) == Claimed_Sum);
    if (!ok){
        std::cout<<"Equal protocol last round failed"<<std::endl;
        return std::make_tuple(ok, Fr(0),Fr(0),Fr(0),Fr(0), r_Challenges);;
    }
    return std::make_tuple(ok, Sumcheck_a1[0], Sumcheck_a2[0], Sumcheck_b1[0],Sumcheck_b2[0], r_Challenges);
}