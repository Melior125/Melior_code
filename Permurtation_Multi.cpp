#include <vector>
#include "Rational_MatrixMul.cpp"
#include <mcl/bn256.hpp>
#include <iostream>
#include <stdexcept>

bool Logup_Permutation_Int(const std::vector<std::vector<Fr>>& f, const std::vector<Fr>& t, const unsigned& nVars){
    int M=1;

    std::vector<Fr> m(1u << nVars,Fr(1)); 

    // P sends oracle of m to V

    // V sends a random field x
    Fr x; x.setRand();
    // P computes M MLE polynomials g1,g2,...,gM 1/(x+f_i(x)) and 1 MLE poly h(x) = m(x)/(x+t(x)) on hypercube 2^nVars
    std::vector<std::vector<Fr>> g(M, std::vector<Fr>(1u<<nVars, Fr(0)));
    std::vector<Fr> h(1u<<nVars, Fr(0));
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<nVars); j++){
            g[i][j] = Fr(1) / (x + f[i][j]);
        }
    }
    for(unsigned int j=0; j<(1u<<nVars); j++){
        h[j] = m[j] / (x + t[j]);
    }
    // P sends all the oracle of g1,g2,...,gM,h to V
    
    // P first runs a sumcheck protocol with V to prove Σ(Σgi(x)-h(x))=0. It's a format of f() sumcheck.
    // Q = Σgi(x)-h(x). Prove ΣQ = 0.
    std::vector<Fr> Q(1u<<nVars, Fr(0));
    Q = h;
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<nVars); j++){
            Q[j] = Q[j] - g[i][j];
        }
    }
    Fr sum =Fr(0);
    for (unsigned int i=0;i<8;i++) {
        sum = sum + Q[i];
    }
    Fr Claimed_Sum = Fr(0);
    Fr point0, point1;
    bool ok = false;
    point0 = Fr(0);
    point1 = Fr(0);
    std::vector<Fr> r_Challenges(nVars,Fr(0));
    for(unsigned int i=0; i<nVars; i++){
        // P computes 2 points and sends them to V
        point0 = Fr(0);
        point1 = Fr(0);
        for(unsigned int j=0; j<(1u<<(nVars-1-i)); j++){
            point0 = point0 + Q[2*j];
            point1 = point1 + Q[2*j+1];
        }
        // V checks 2 points sum = claimed_sum
        ok = (point0+point1 == Claimed_Sum);
        if (!ok) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = r_i * point1 + (1-r_i)*point0;
        // P maintains bkp table
        Q = Int_ri_Table_Compute_fx(nVars-i,Q,r_i);
    }

    if(!ok) return ok;

    std::vector<Fr> r2 = RandomFieldChallenge_Generator(nVars);
    std::vector<Fr> random_lambda_scalar = RandomFieldChallenge_Generator(M+1);
   
    std::vector<Fr> eq(1u<<nVars,Fr(1));    
    for (std::size_t i = 0; i < (1u<<nVars); i++) {
        std::vector<int> index(nVars);
        index = indexToBits(i,nVars);
        for (std::size_t j = 0; j < nVars; j++) {
            Fr term1 = r2[j] * Fr(index[j]);         // e_i * x_i
            Fr term2 = (Fr(1) - r2[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
        eq[i] = eq[i] * (term1 + term2);
        }
    }
    // P runs sumcheck with V
    int max_degree = 3;
    Claimed_Sum = Fr(0);
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges2(nVars,Fr(0));
    std::vector<std::vector<Fr>> Sumcheck_f = f;
    std::vector<std::vector<Fr>> Sumcheck_g = g;
    std::vector<Fr> Sumcheck_t = t;
    std::vector<Fr> Sumcheck_h = h;
    std::vector<Fr> Sumcheck_m = m;
    std::vector<Fr> Sumcheck_eq = eq;
    for(unsigned int i=0; i<nVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<std::vector<Fr>>> Auxiliary_f(max_degree+1, std::vector<std::vector<Fr>>(M, std::vector<Fr>(1<<(nVars-1-i),Fr(0))));
        std::vector<std::vector<std::vector<Fr>>> Auxiliary_g(max_degree+1, std::vector<std::vector<Fr>>(M, std::vector<Fr>(1<<(nVars-1-i),Fr(0))));
        // std::cout<<"Auxiliary_f init done"<<std::endl;
        for (unsigned jj=0;jj<M;jj++){
            for (unsigned kk=0;kk<(1u<<(nVars-1-i));kk++){
                Auxiliary_f[0][jj][kk] = Sumcheck_f[jj][kk*2];
                Auxiliary_f[1][jj][kk] = Sumcheck_f[jj][kk*2+1];
                Auxiliary_g[0][jj][kk] = Sumcheck_g[jj][kk*2];
                Auxiliary_g[1][jj][kk] = Sumcheck_g[jj][kk*2+1];
            }
        }
        for (unsigned j=2;j<max_degree+1;j++){
            for (unsigned jj=0;jj<M;jj++){
                Auxiliary_f[j][jj] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_f[jj], Fr(j));
                Auxiliary_g[j][jj] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_g[jj], Fr(j));
            }
        }
        std::vector<std::vector<Fr>> Auxiliary_t(max_degree+1, std::vector<Fr>(1<<(nVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_h(max_degree+1, std::vector<Fr>(1<<(nVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(nVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_m(max_degree+1, std::vector<Fr>(1<<(nVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(nVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_t[j] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_t, Fr(j));
            Auxiliary_h[j] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_h, Fr(j));
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_m[j] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_m, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(nVars-1-i));kk++){
            Auxiliary_t[0][kk] = Sumcheck_t[kk*2];
            Auxiliary_t[1][kk] = Sumcheck_t[kk*2+1];
            Auxiliary_h[0][kk] = Sumcheck_h[kk*2];
            Auxiliary_h[1][kk] = Sumcheck_h[kk*2+1];
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_m[0][kk] = Sumcheck_m[kk*2];
            Auxiliary_m[1][kk] = Sumcheck_m[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(nVars-1-i)); jj++){
                for(unsigned int kk=0; kk<M; kk++){
                    result[j][jj] = result[j][jj] + Auxiliary_eq[j][jj] * random_lambda_scalar[kk] * (Auxiliary_g[j][kk][jj]*(x+Auxiliary_f[j][kk][jj])-1);
                }
                result[j][jj] = result[j][jj] + Auxiliary_eq[j][jj] * random_lambda_scalar[M] * (Auxiliary_h[j][jj]*(x+Auxiliary_t[j][jj])-Auxiliary_m[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(nVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges2[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        for (unsigned jj=0;jj<M;jj++){
            Sumcheck_f[jj] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_f[jj], r_i);
            Sumcheck_g[jj] = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_g[jj], r_i);
        }
        Sumcheck_t = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_t, r_i);
        Sumcheck_eq = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_eq, r_i);
        Sumcheck_m = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_m, r_i);
        Sumcheck_h = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_h, r_i);
    }


    return ok;
}

bool Int_Permurtation_Multi(const std::vector<Fr>& f, const std::vector<Fr>& g, const unsigned& nVars){
    // V generates a random field gama
    Fr gama;gama.setRand();
    // P computes the Claimed_Mul
    Fr Claimed_Mul1 = Fr(1);
    Fr Claimed_Mul2 = Fr(1);
    for (unsigned int i=0; i<(1u<<nVars);i++){
        Claimed_Mul1 = Claimed_Mul1 * f[i];
        Claimed_Mul2 = Claimed_Mul2 * g[i];
    }
    bool ok=false;
    ok = (Claimed_Mul1 == Claimed_Mul2);
    if (!ok) return ok;
    // P computes the whole multi tree V_f and V_g 
    std::vector<std::vector<Fr>> V_f(nVars+1,std::vector<Fr>(1u<<nVars,Fr(0)));
    std::vector<std::vector<Fr>> V_g(nVars+1,std::vector<Fr>(1u<<nVars,Fr(0)));
    V_f[0] = f;
    V_g[0] = g;
    for (unsigned int i=1;i<=nVars;i++){
        for (unsigned int j=0;j<((1<<nVars-i));j++){
            V_f[i][j] = V_f[i-1][2*j] * V_f[i-1][2*j+1];
            V_g[i][j] = V_g[i-1][2*j] * V_g[i-1][2*j+1];
        }
    }
    std::cout<<"before mul tree ok"<<std::endl;
    for (unsigned int i=1;i<=nVars;i++){

        
        // V generates a random index
        std::vector<Fr> z_i = RandomFieldChallenge_Generator(nVars-i);
        // P computes the eq
        std::vector<Fr> eq(1u<<(nVars-i),Fr(1));
        for (std::size_t ii = 0; ii < (1u<<(nVars-i)); ii++) {
            std::vector<int> index(nVars-i);
            index = indexToBits(ii,nVars-i);
            for (std::size_t j = 0; j < nVars-i; j++) {
                Fr term1 = z_i[j] * Fr(index[j]);         // e_i * x_i
                Fr term2 = (Fr(1) - z_i[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
            eq[ii] = eq[ii] * (term1 + term2);
            }
        }
        std::vector<Fr> Sumcheck_Vi_f(1u<<(nVars-i),Fr(0));
        std::vector<Fr> Sumcheck_eq = eq;
        std::vector<Fr> Sumcheck_Vi_minus_0_f(1u<<(nVars-i),Fr(0));
        std::vector<Fr> Sumcheck_Vi_minus_1_f(1u<<(nVars-i),Fr(0));
        for (unsigned j=0;j<(1u<<(nVars-i));j++){
            Sumcheck_Vi_minus_0_f[j] = V_f[i-1][2*j];
            Sumcheck_Vi_minus_1_f[j] = V_f[i-1][2*j+1];
        }
        for (unsigned int j=0;j<(1u<<(nVars-i));j++) Sumcheck_Vi_f[j] = Sumcheck_Vi_minus_0_f[j] * Sumcheck_Vi_minus_1_f[j];
 

        std::cout<<"before sumcheck ok"<<std::endl;
        // P claim a sum
        Fr Claimed_Sum = Fr(0);
        int max_degree = 2;
        std::vector<Fr> r_Challenges(nVars-i,Fr(0));
        
        for (unsigned int j=0;j<(nVars-i);j++){
            // P computes max_degree+1 points and sends them to V
            std::vector<std::vector<Fr>> Auxiliary_Vi_f(max_degree+1, std::vector<Fr>(1<<(nVars-1-i-j),Fr(0)));
            std::vector<std::vector<Fr>> Auxiliary_Vi_minus_0_f(max_degree+1, std::vector<Fr>(1<<(nVars-1-i-j),Fr(0)));
            std::vector<std::vector<Fr>> Auxiliary_Vi_minus_1_f(max_degree+1, std::vector<Fr>(1<<(nVars-1-i-j),Fr(0)));
            std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(nVars-1-i-j),Fr(0)));

            for (unsigned jj=2;jj<max_degree+1;jj++){
                Auxiliary_eq[jj] = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_eq, Fr(jj));
                Auxiliary_Vi_f[jj] = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_f, Fr(jj));
                Auxiliary_Vi_minus_0_f[jj] = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_minus_0_f, Fr(jj));
                Auxiliary_Vi_minus_1_f[jj] = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_minus_1_f, Fr(jj));
            }

            for (unsigned jj=0;jj<(1u<<(nVars-1-i-j));jj++){
                Auxiliary_eq[0][jj] = Sumcheck_eq[jj*2];
                Auxiliary_eq[1][jj] = Sumcheck_eq[jj*2+1];
                Auxiliary_Vi_minus_0_f[0][jj] = Sumcheck_Vi_minus_0_f[jj*2];
                Auxiliary_Vi_minus_0_f[1][jj] = Sumcheck_Vi_minus_0_f[jj*2+1];
                Auxiliary_Vi_minus_1_f[0][jj] = Sumcheck_Vi_minus_1_f[jj*2];
                Auxiliary_Vi_minus_1_f[1][jj] = Sumcheck_Vi_minus_1_f[jj*2+1];
                Auxiliary_Vi_f[0][jj] = Sumcheck_Vi_f[jj*2];
                Auxiliary_Vi_f[1][jj] = Sumcheck_Vi_f[jj*2+1];
            }

            std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(nVars-1-i-j),Fr(0)));
            std::vector<Fr> result_sum(max_degree+1, Fr(0));
            for (unsigned int jj =0; jj<max_degree+1;jj++){
                std::cout<<result_sum[jj]<<" ";
            }
            for(unsigned int jj=0; jj<max_degree+1; jj++){
                for(unsigned int jjj=0; jjj<(1u<<(nVars-1-i-j)); jjj++){
                    result[jj][jjj] = Auxiliary_eq[jj][jjj] * ((Auxiliary_Vi_minus_0_f[jj][jjj] * Auxiliary_Vi_minus_1_f[jj][jjj]) - Auxiliary_Vi_f[jj][jjj]);
                }
            }
            for(unsigned int jj=0; jj<max_degree+1; jj++){
                for(unsigned int jjj=0; jjj<(1u<<(nVars-1-i-j)); jjj++){
                    result_sum[jj] = result_sum[jj] + result[jj][jjj];
                }
            }
            std::cout<<"result ok"<<std::endl;
            // V checks 2 points sum = claimed_sum

            ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
            if (!ok) break;
            // V generates random r_i and sends it to P. V computes next Claimed_Sum.
            Fr r_j;r_j.setRand();
            r_Challenges[j] = r_j;
            Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_j,max_degree);

            // P maintains bkp table
            Sumcheck_eq = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_eq, r_j);
            Sumcheck_Vi_f = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_f, r_j);
            Sumcheck_Vi_minus_0_f = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_minus_0_f, r_j);
            Sumcheck_Vi_minus_1_f = Int_ri_Table_Compute_fx(nVars-i-j, Sumcheck_Vi_minus_1_f, r_j);
            std::cout<<"bkp table ok"<<std::endl;
        }
  

        if (!ok) break;
        std::cout<<"round"<<i<<"sumcheck success"<<std::endl;
    }
    return ok;
}



int main(){
    initPairing();
    std::vector<Fr> f(8,Fr(1));
    std::vector<Fr> g(8,Fr(1));
    int nVars = 3;
    f[0] = Fr(5);
    f[1] = Fr(4);
    f[2] = Fr(3);
    f[6] = Fr(2);
    g[3] = Fr(2);
    g[4] = Fr(3);
    g[5] = Fr(4);
    g[6] = Fr(5);
    bool ok =false;
    for (unsigned int i=0;i<8;i++) {
        std::cout<<f[i]<<" ";
    }
    std::cout<<std::endl;
    for (unsigned int i=0;i<8;i++) {
        std::cout<<g[i]<<" ";
    }
    std::cout<<std::endl;
    std::vector<std::vector<Fr>> f_1(1,std::vector<Fr>(8,Fr(0)));
    f_1[0] = f;
    std::cout<<"init success"<<std::endl;
    // ok = Int_Permurtation_Multi(f,g,nVars);
    // std::cout<<ok<<std::endl;
    ok = Logup_Permutation_Int(f_1,g,nVars);
    std::cout<<ok<<std::endl;
    return 0;
}