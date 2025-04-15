#include <vector>
#include "head/Rational_Fr.hpp"
#include "head/IOracleRational.hpp"
#include <mcl/bn256.hpp>
#include "pcs.hpp" 

vector<Fr> computeEqA(long long L, vector<Fr> r){
    unsigned int totalBits = L;
    unsigned int N = 1u << totalBits;  // 2^(nVars + mVars)
    std::vector<Fr> eqA(N, Fr(0));
    eqA[0] = Fr(1);
    for (unsigned int j = 0; j < totalBits; j++) {
        unsigned int halfSize = 1u << j; 
        for (unsigned int i = 0; i < halfSize; i++) {
            Fr oldVal = eqA[i];
            eqA[i + halfSize] = oldVal * r[j];
            eqA[i] = oldVal * (Fr(1) - r[j]);
        }
    }

    return eqA;
    
}

static std::vector<int> indexToBits(size_t idx, unsigned int n) {
    std::vector<int> bits(n, 0);
    for(unsigned int i=0; i<n; i++){
        bits[i] = (idx >> i)&1;
    }
    return bits;
}

static int bitsToIndex(const std::vector<int>& bits) {
    int idx = 0;
    for (size_t i = 0; i < bits.size(); i++) {
        idx |= (bits[i] << i); 
    }
    return idx;
}

Fr Int_Multi_evaluate(const std::vector<Fr>& f, const std::vector<Fr>& r, const unsigned& yVars) {
    std::vector<Fr> current = f;

    // 逐步插值
    for (int i = 0; i < yVars; i++) {
        std::vector<Fr> next(1u<<(yVars-1-i),Fr(0));
        for (size_t j = 0; j < 1u<<(yVars-1-i); j++) {
            next[j] = (Fr(1) - r[i]) * current[2 * j] + r[i] * current[2 * j + 1];
        }
        current = next;
    }
    return current[0]; 
}
Fr Int_Multi_evaluate_ll(const std::vector<ll>& f, const std::vector<Fr>& r, const unsigned& yVars) {
    std::vector<Fr> current(1u<<yVars);
    for (unsigned int i=0;i<(1u<<yVars);i++){
        current[i] = Fr(f[i]);
    }


    for (int i = 0; i < yVars; i++) {
        std::vector<Fr> next(1u<<(yVars-1-i),Fr(0));
        for (size_t j = 0; j < 1u<<(yVars-1-i); j++) {
            next[j] = (Fr(1) - r[i]) * current[2 * j] + r[i] * current[2 * j + 1];
        }
        current = next;
    }
    return current[0]; 
}

Rational_Fr Rational_Multi_evaluate(const std::vector<Rational_Fr>& f, const std::vector<Fr>& r, const unsigned& yVars) {
    std::vector<Rational_Fr> current = f;


    for (int i = 0; i < yVars; i++) {
        std::vector<Rational_Fr> next(1u<<(yVars-1-i));
        for (size_t j = 0; j < 1u<<(yVars-1-i); j++) {
            next[j] = Rational_Fr((Fr(1) - r[i]),1) * current[2 * j] + Rational_Fr(r[i],1) * current[2 * j + 1];
        }
        current = next;
    }
    return current[0];
}

Fr Int_lagrangeInterpolation(const std::vector<Fr>& x, const Fr& r, const unsigned& n) {
    
    Fr result = Fr(0);

    for (int i = 0; i <= n; i++) {
        Fr term = x[i]; // P(x_i)
        for (int j = 0; j <= n; j++) {
            if (i != j) {
                term *= (r - Fr(j)) / (Fr(i) - Fr(j));
            }
        }
        result += term;
    }

    return result;
}

Rational_Fr Rational_lagrangeInterpolation(const std::vector<Rational_Fr>& x, const Fr& r, const unsigned& n) {

    Rational_Fr result;

    for (int i = 0; i <= n; i++) {
        Rational_Fr term = x[i]; // P(x_i)
        for (int j = 0; j <= n; j++) {
            if (i != j) {
                term = term * Rational_Fr((r - Fr(j)),1) / Rational_Fr((Fr(i) - Fr(j)),1);
            }
        }
        result = result + term;
    }

    return result;
}

std::vector<Fr> Int_ri_Table_Compute_fx(unsigned int n, const std::vector<Fr>& T, const Fr& r){
    std::vector<Fr> ri_T(1<<(n-1));

    for(unsigned int j=0; j<(1<<(n-1)); j++){
        ri_T[j] = T[2*j] + (T[2*j+1] - T[2*j])* r;
    }
    return ri_T;
};

std::vector<Rational_Fr> Rational_ri_Table_Compute_fx(unsigned int n, const std::vector<Rational_Fr>& T, const Fr& r){
    unsigned sizeT = T.size(); // 2^n
    Rational_Fr rVal(r, Fr(1)); 
    size_t halfSize = sizeT / 2;
    std::vector<Rational_Fr> ri_T(halfSize);

    for(size_t j=0; j<halfSize; j++){
        auto t0 = T[2*j];
        auto t1 = T[2*j+1];
        auto diff = Rational_Fr::sub(t1, t0);
        ri_T[j] = Rational_Fr::add(t0, Rational_Fr::mul(diff, rVal));
    }
    return ri_T;
};


Rational_Fr getSumOfPairs(unsigned sizeT, const std::vector<Rational_Fr>& T){
    Rational_Fr sum;
    for(size_t j=0; j<sizeT; j+=2) {
        auto pairSum = Rational_Fr::add(T[j], T[j+1]);
        sum = Rational_Fr::add(sum, pairSum);
    }
    return sum;
}

std::tuple<bool, Fr,Fr,Fr,Fr,Fr,std::vector<Fr>> Designed_Int_Sumcheck_for_Rational(const std::vector<Fr>& f, const std::vector<Fr>& g, const std::vector<Fr>& h, const std::vector<Fr>& gg, const std::vector<Fr>& hh,
    const Fr& ClaimedValue, const unsigned& kVars, const Fr& lambda){
    // 依次：eq, p_k+1_0, q_k+1_0, p_k+1_1, q_k+1_1
    // P claims ClaimedValue
    Fr Claimed_Sum = ClaimedValue;
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
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_f[j][jj] * (Auxiliary_g[j][jj]* Auxiliary_hh[j][jj] + Auxiliary_gg[j][jj]* Auxiliary_h[j][jj]) + 
                lambda * Auxiliary_f[j][jj] * Auxiliary_h[j][jj]* Auxiliary_hh[j][jj];
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) break;
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
    ok == ((Sumcheck_f[0]*(Sumcheck_g[0]*Sumcheck_hh[0] + Sumcheck_gg[0]*Sumcheck_h[0]) + lambda * Sumcheck_f[0] * Sumcheck_h[0]*Sumcheck_hh[0]) == Claimed_Sum);
    return std::make_tuple(ok, Sumcheck_f[0], Sumcheck_g[0], Sumcheck_h[0], Sumcheck_gg[0], Sumcheck_hh[0], r_Challenges);
}


std::tuple<bool, Fr, Fr, std::vector<Fr>> RationalSumcheck_fx(
    const std::vector<Fr>& num,
    const std::vector<Fr>& den,
    const std::vector<Rational_Fr>& fx,
    // const std::vector<std::vector<Rational_Fr>>& witness,
    const Rational_Fr& claimedSum,
    unsigned int nVars
){
    // currentPartialSum <- claimedSum
    std::vector<std::vector<Rational_Fr>> witness(nVars+1,std::vector<Rational_Fr>(1u<<nVars));
    std::vector<Rational_Fr> T = fx;
    witness[nVars] = T;
    for (unsigned int i=0;i<nVars;i++) {
        std::vector<Rational_Fr> T_half(1u<<(nVars-1-i));
        for (unsigned int j=0;j<(1u<<(nVars-1-i));j++){
            T_half[j] = T[2*j] + T[2*j+1];
        }
        T = T_half;
        witness[nVars-1-i] = T;
    }
    Fr Claimed_pk = claimedSum.numerator;
    Fr Claimed_qk = claimedSum.denominator;

    //Round1
    //Prover claims p1(0)p1(1)q1(0)q1(1)
    Rational_Fr point0,point1;
    point0 = witness[1][0];
    point1 = witness[1][1];
    Fr p_1_0,p_1_1,q_1_0,q_1_1;
    std::vector<Fr> rChallenges(nVars, Fr(0));
    p_1_0 = point0.numerator; p_1_1 = point1.numerator;
    q_1_0 = point0.denominator; q_1_1 = point1.denominator;
    // V verifies it.
    bool ok = false;
    ok = ((p_1_0 * q_1_1 + p_1_1 * q_1_0) * Claimed_qk) == (Claimed_pk *q_1_0*q_1_1 ) ;
    if (!ok) {
        std::cout<<"round 1 failed"<<std::endl;
        return std::make_tuple(false, Fr(0), Fr(0), rChallenges);
    }
    // V generates first random r_1 and computes pk,qk(i.e. q1(r),p1(r) here)
    rChallenges[0].setRand();
    Claimed_pk = (1-rChallenges[0]) * p_1_0 + rChallenges[0] * p_1_1;
    Claimed_qk = (1-rChallenges[0]) * q_1_0 + rChallenges[0] * q_1_1;
    for (unsigned int round=1;round<nVars;round++){
        // P computes eq
        std::vector<Fr> eq(1u<<round,Fr(1));    
        for (std::size_t i = 0; i < (1u<<round); i++) {
            std::vector<int> index(round);
            index = indexToBits(i,round);
            for (std::size_t j = 0; j < round; j++) {
                Fr term1 = rChallenges[j] * Fr(index[j]);         // e_i * x_i
                Fr term2 = (Fr(1) - rChallenges[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
                eq[i] = eq[i] * (term1 + term2);
            }
        }
        // P computes p_k+1_j_0, p_k+1_j_1, q_k+1_j_0, q_k+1_j_1 from witness
        std::vector<Fr> p_kplus1_0(1u<<round,Fr(0)), p_kplus1_1(1u<<round,Fr(0));
        std::vector<Fr> q_kplus1_0(1u<<round,Fr(0)), q_kplus1_1(1u<<round,Fr(0));
        for (unsigned int i=0;i<(1u<<round);i++){
            p_kplus1_0[i] = witness[round+1][2*i].numerator;
            q_kplus1_0[i] = witness[round+1][2*i].denominator;
            p_kplus1_1[i] = witness[round+1][2*i+1].numerator;
            q_kplus1_1[i] = witness[round+1][2*i+1].denominator;
        }
        // V generates the random lambda_k
        Fr lambda_k; lambda_k.setRand();
        //  Prover and V runs sumcheck_fx_gx_hx to prove the rational computation relation
        std::tuple<bool,Fr,Fr,Fr,Fr,Fr,std::vector<Fr>> ok1 = Designed_Int_Sumcheck_for_Rational(eq,p_kplus1_0,q_kplus1_0,p_kplus1_1,q_kplus1_1,Claimed_pk + lambda_k*Claimed_qk,round,lambda_k);
        if (!std::get<0>(ok1)){
            std::cout<<"Rational Sumcheck failed because round "<<round<<"Designed Sumcheck failed!"<<std::endl;
            return std::make_tuple(false, Fr(0), Fr(0), rChallenges);
        }
        // V can easily check eq by himself
        // V need to open p_k+1_0, q_k+1_0, p_k+1_1, q_k+1_1; V generates a random field to batch it
        std::vector<Fr> new_challenge(round+1,Fr(0));
        new_challenge[0].setRand();
        for (unsigned i=1;i<=round;i++){
            new_challenge[i] = std::get<6>(ok1)[i-1];
        }
        rChallenges = new_challenge;
        // P claimes batched result
        Claimed_pk = (1-new_challenge[0]) * std::get<2>(ok1) + new_challenge[0] * std::get<4>(ok1);
        Claimed_qk = (1-new_challenge[0]) * std::get<3>(ok1) + new_challenge[0] * std::get<5>(ok1);
        // V checks this combinition; Obviously right
        // into next round of sumcheck: prove p_k+1_r_k+1 and q_k+1_r_k+1
    }
    return std::make_tuple(true, Claimed_pk,Claimed_qk, rChallenges);
}


std::vector<Fr> RandomFieldChallenge_Generator(int n){
    std::vector<Fr> rChallenges(n);
    for (unsigned i=0;i<n;i++){
        Fr r_i; r_i.setRand();
        rChallenges[i] = r_i;
    }
    return rChallenges;
}

Rational_Fr getSumOfPairs_fx_gx(unsigned sizeT, const std::vector<Rational_Fr>& T_f, const std::vector<Rational_Fr>& T_g){
    Rational_Fr sum; // 默认= 0/1
    for(size_t j=0; j<sizeT; j+=2) {
        auto pairSum = Rational_Fr::add(Rational_Fr::mul(T_f[j],T_g[j]), Rational_Fr::mul(T_f[j+1],T_g[j+1]));
        sum = Rational_Fr::add(sum, pairSum);
    }
    return sum;
}

std::tuple<bool, Fr, Fr, std::vector<Fr>> Int_Sumcheck_fx_gx(const std::vector<Fr>& f, const std::vector<Fr>& g, const Fr& ClaimedValue, const unsigned& kVars){
    // P claims ClaimedValue
    Fr Claimed_Sum = ClaimedValue;
    // P computes 3 points and sends them to V
    int max_degree = 2;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(kVars,Fr(0));
    std::vector<Fr> Sumcheck_f = f;
    std::vector<Fr> Sumcheck_g = g;
    for(unsigned int i=0; i<kVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_f(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_g(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(1)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_f[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, Fr(j));
            Auxiliary_g[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_f[0][kk] = Sumcheck_f[kk*2];
            Auxiliary_f[1][kk] = Sumcheck_f[kk*2+1];
            Auxiliary_g[0][kk] = Sumcheck_g[kk*2];
            Auxiliary_g[1][kk] = Sumcheck_g[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = result[j][jj] * Auxiliary_f[j][jj] * Auxiliary_g[j][jj];
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_f = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, r_i);
        Sumcheck_g = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, r_i);
    }
    ok = (Sumcheck_f[0] * Sumcheck_g[0] == Claimed_Sum);
    return std::make_tuple(ok, Sumcheck_f[0], Sumcheck_g[0], r_Challenges);
}

std::tuple<bool, Fr, Fr,Fr,Fr,Fr,Fr,Fr, std::vector<Fr>> Designed_Int_Sumcheck_for_Rational_Hadamard_fghw(const std::vector<Fr>& A1, const std::vector<Fr>& A2, 
    const std::vector<Fr>& B1,const std::vector<Fr>& B2,const std::vector<Fr>& C1,const std::vector<Fr>& C2,const std::vector<Fr>& eq, const Fr& ClaimedValue, const unsigned& kVars){
    // P claims ClaimedValue
    Fr Claimed_Sum = ClaimedValue;
    // P computes 4 points and sends them to V
    int max_degree = 4;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(kVars,Fr(0));
    std::vector<Fr> Sumcheck_a1 = A1;
    std::vector<Fr> Sumcheck_a2 = A2;
    std::vector<Fr> Sumcheck_b1 = B1;
    std::vector<Fr> Sumcheck_b2 = B2;
    std::vector<Fr> Sumcheck_c1 = C1;
    std::vector<Fr> Sumcheck_c2 = C2;
    std::vector<Fr> Sumcheck_eq = eq;
    for(unsigned int i=0; i<kVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_a1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_c1(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_c2(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_a1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, Fr(j));
            Auxiliary_a2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, Fr(j));
            Auxiliary_b1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, Fr(j));
            Auxiliary_b2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, Fr(j));
            Auxiliary_c1[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_c1, Fr(j));
            Auxiliary_c2[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_c2, Fr(j));
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_a1[0][kk] = Sumcheck_a1[kk*2];
            Auxiliary_a1[1][kk] = Sumcheck_a1[kk*2+1];
            Auxiliary_a2[0][kk] = Sumcheck_a2[kk*2];
            Auxiliary_a2[1][kk] = Sumcheck_a2[kk*2+1];
            Auxiliary_b1[0][kk] = Sumcheck_b1[kk*2];
            Auxiliary_b1[1][kk] = Sumcheck_b1[kk*2+1];
            Auxiliary_b2[0][kk] = Sumcheck_b2[kk*2];
            Auxiliary_b2[1][kk] = Sumcheck_b2[kk*2+1];
            Auxiliary_c1[0][kk] = Sumcheck_c1[kk*2];
            Auxiliary_c1[1][kk] = Sumcheck_c1[kk*2+1];
            Auxiliary_c2[0][kk] = Sumcheck_c2[kk*2];
            Auxiliary_c2[1][kk] = Sumcheck_c2[kk*2+1];
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_a1[j][jj] * Auxiliary_b1[j][jj]* Auxiliary_c2[j][jj] - Auxiliary_c1[j][jj] * Auxiliary_a2[j][jj]* Auxiliary_b2[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_a1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a1, r_i);
        Sumcheck_a2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a2, r_i);
        Sumcheck_b1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b1, r_i);
        Sumcheck_b2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b2, r_i);
        Sumcheck_c1 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_c1, r_i);
        Sumcheck_c2 = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_c2, r_i);
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
    }
    ok == (Sumcheck_eq[0] * ( Sumcheck_a1[0]*Sumcheck_b1[0]*Sumcheck_c2[0] -Sumcheck_c1[0]*Sumcheck_a2[0]*Sumcheck_b2[0]) == Claimed_Sum);
    return std::make_tuple(ok, Sumcheck_a1[0], Sumcheck_a2[0], Sumcheck_b1[0], Sumcheck_b2[0],Sumcheck_c1[0], Sumcheck_c2[0],Sumcheck_eq[0], r_Challenges);
}

std::tuple<bool, Fr,Fr,Fr, std::vector<Fr>> Int_Sumcheck_fx_gx_hx(const std::vector<Fr>& f, const std::vector<Fr>& g, const std::vector<Fr>& h, const Fr& ClaimedValue, const unsigned& kVars){
    // P claims ClaimedValue
    Fr Claimed_Sum = ClaimedValue;
    // P computes 4 points and sends them to V
    int max_degree = 3;
    bool ok = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(kVars,Fr(0));
    std::vector<Fr> Sumcheck_f = f;
    std::vector<Fr> Sumcheck_g = g;
    std::vector<Fr> Sumcheck_h = h;
    for(unsigned int i=0; i<kVars; i++){
        // P computes max_degree+1 points and sends them to V
        // t.start();
        std::vector<std::vector<Fr>> Auxiliary_f(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_g(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_h(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            // t.start();
            Auxiliary_f[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, Fr(j));
            Auxiliary_h[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_h, Fr(j));
            Auxiliary_g[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, Fr(j));
            // t.stop("Fr(j)",true,false);
        }
        // t.start();
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_f[0][kk] = Sumcheck_f[kk*2];
            Auxiliary_f[1][kk] = Sumcheck_f[kk*2+1];
            Auxiliary_h[0][kk] = Sumcheck_h[kk*2];
            Auxiliary_h[1][kk] = Sumcheck_h[kk*2+1];
            Auxiliary_g[0][kk] = Sumcheck_g[kk*2];
            Auxiliary_g[1][kk] = Sumcheck_g[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + Auxiliary_f[j][jj] * Auxiliary_h[j][jj]* Auxiliary_g[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        // t.start();
        Sumcheck_f = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_f, r_i);
        Sumcheck_g = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_g, r_i);
        Sumcheck_h = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_h, r_i);
        // t.stop("r_i",true,false);
    }
    ok == (Sumcheck_f[0]*Sumcheck_g[0]*Sumcheck_h[0] == Claimed_Sum);
    return std::make_tuple(ok, Sumcheck_f[0], Sumcheck_g[0], Sumcheck_h[0], r_Challenges);
}

std::vector<Fr> convertToFrVector(const ll* arr, size_t size) {
    std::vector<Fr> result(size);
    for (size_t i = 0; i < size; ++i) {
        result[i] = Fr(arr[i]); 
    }
    return result;
}