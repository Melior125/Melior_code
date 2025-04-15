#include <vector>

#include "MatrixMul.cpp"
#include <mcl/bn256.hpp>
#include <iostream>
#include <stdexcept>

namespace std {
    template<>
    struct hash<Fr> {
        std::size_t operator()(const Fr& x) const
        {

            unsigned char buf[32];
            const size_t n = x.serialize(buf, sizeof(buf));
            std::size_t h = 0;
            for (size_t i = 0; i < n; i++) {
                h = (h * 131542391u) ^ buf[i];
            }
            return h;
        }
    };
    } // namespace std
    
void padVectors(std::vector<std::vector<Fr>>& vec, size_t targetSize) {
    if (vec.size() >= targetSize) return;
    std::vector<Fr> lastElement = vec.back();
    while (vec.size() < targetSize) {
        vec.push_back(lastElement);
    }
}

std::tuple<bool, std::vector<Fr>,Fr,std::vector<Fr>> Logup_Value_Lookup_Int(const std::vector<std::vector<Fr>>& f, const std::vector<Fr>& t, const unsigned& M, const unsigned& nVars,G1&G,G1*g_big){
    std::unordered_map<Fr, std::size_t> dict_f;
    dict_f.reserve(1u << nVars);
    for (const auto& fi : f) {
        for (const auto& val : fi) {
            ++dict_f[val];  
        }
    }
    std::unordered_map<Fr, std::size_t> dict_t;
    dict_t.reserve(1u << nVars);
    for (const auto& val : t) {
        ++dict_t[val];
    }

    const std::size_t size_m = (1u << nVars); 
    std::vector<Fr> m(size_m, Fr(0));  
    for (std::size_t i = 0; i < size_m; ++i) {
        const Fr& key = t[i];
        

        auto itF = dict_f.find(key);
        auto itT = dict_t.find(key);
        

        if (itF == dict_f.end() || itT == dict_t.end() || itT->second == 0) {
            m[i] = Fr(0);
        } else {

            Fr numerator   = Fr(itF->second); 
            Fr denominator = Fr(itT->second);
            Fr invDen;
            Fr::inv(invDen, denominator); 
            m[i] = numerator * invDen;   
        }
    }

    G1* commitM = prover_commit_Fr(m.data(),g_big,nVars,16);
    Fr x; x.setRand();
    std::vector<std::vector<Fr>> g(M, std::vector<Fr>(1u<<nVars, Fr(0)));
    std::vector<Fr> h(1u<<nVars, Fr(0));
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<nVars); j++){
            g[i][j] = Fr(1) / (x + f[i][j]);
        }
    }
    // std::cout<<"g computed"<<std::endl;
    for(unsigned int j=0; j<(1u<<nVars); j++){
        h[j] = m[j] / (x + t[j]);
    }
    // P sends all the oracle of g1,g2,...,gM,h to V
    std::vector<G1*> commitg(M);
    for (unsigned int i=0;i<M;i++){
        commitg[i] = prover_commit_Fr(g[i].data(),g_big,nVars,16);
    }
    G1* commitH = prover_commit_Fr(h.data(),g_big,nVars,16);
    std::vector<Fr> Q(1u<<nVars, Fr(0));
    Q = h;
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<nVars); j++){
            Q[j] = Q[j] - g[i][j];
        }
    }
    Fr Claimed_Sum = Fr(0);
    Fr point0, point1;
    bool ok = false;
    point0 = Fr(0);
    point1 = Fr(0);
    std::vector<Fr> r_Challenges(nVars,Fr(0));
    for(unsigned int i=0; i<nVars; i++){
        point0 = Fr(0);
        point1 = Fr(0);
        for(unsigned int j=0; j<(1u<<(nVars-1-i)); j++){
            point0 = point0 + Q[2*j];
            point1 = point1 + Q[2*j+1];
        }
        ok = (point0+point1 == Claimed_Sum);
        if (!ok) break;
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = r_i * point1 + (1-r_i)*point0;
        Q = Int_ri_Table_Compute_fx(nVars-i,Q,r_i);
    }
    std::vector<Fr> Claimedg(M,Fr(0));
    for (unsigned int i=0;i<M;i++){
        Claimedg[i] = Int_Multi_evaluate(g[i],r_Challenges,nVars);
    }
    Fr Claimedh = Fr(0);
    Claimedh = Int_Multi_evaluate(h,r_Challenges,nVars);
    Fr check_h_g_sum=Claimedh;
    for (unsigned int i=0;i<M;i++){
        check_h_g_sum = check_h_g_sum - Claimedg[i];
    }
    ok = (check_h_g_sum == Claimed_Sum);
    if(!ok) {
        std::cout<<"sigma_g == h failed"<<std::endl;
        return std::make_tuple(false,r_Challenges,Fr(0),r_Challenges);
    }
    for (unsigned int i=0;i<M;i++){
        openCommit(g[i],r_Challenges.data(),Claimedg[i],G,g_big,commitg[i],nVars);
    }
    openCommit(h,r_Challenges.data(),Claimedh,G,g_big,commitH,nVars);
    std::vector<Fr> r2 = RandomFieldChallenge_Generator(nVars);
    std::vector<Fr> random_lambda_scalar = RandomFieldChallenge_Generator(M+1);
    std::vector<Fr> eq(1u<<nVars,Fr(1));    
    for (std::size_t i = 0; i < (1u<<nVars); i++) {
        std::vector<int> index(nVars);
        index = indexToBits(i,nVars);
        for (std::size_t j = 0; j < nVars; j++) {
            Fr term1 = r2[j] * Fr(index[j]); 
            Fr term2 = (Fr(1) - r2[j]) * Fr(1 - index[j]); 
        eq[i] = eq[i] * (term1 + term2);
        }
    }
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
    Fr checker2 = Fr(0);
    for (unsigned int i=0;i<M;i++){
        checker2 = checker2 + Sumcheck_eq[0] * random_lambda_scalar[i] * (Sumcheck_g[i][0]*(x+Sumcheck_f[i][0])-Fr(1));
    }
    checker2 = checker2 + Sumcheck_eq[0] * random_lambda_scalar[M] * (Sumcheck_h[0]*(x+Sumcheck_t[0])-Sumcheck_m[0]);
    ok = (checker2 == Claimed_Sum);
    if (!ok) {
        std::cout<<"P's last round claim failed"<<std::endl;
        return std::make_tuple(false,r_Challenges,Fr(0),r_Challenges);
    }
    for (unsigned int i=0;i<M;i++){
        openCommit(g[i],r_Challenges2.data(),Sumcheck_g[i][0],G,g_big,commitg[i],nVars);
    }
    // std::cout<<"all the g PCS open correct"<<std::endl;
    // openCommit(m,r_Challenges2.data(),Sumcheck_m[0],G,g_big,commitM,nVars);
    // std::cout<<"m PCS open correct"<<std::endl;
    openCommit(h,r_Challenges2.data(),Sumcheck_h[0],G,g_big,commitH,nVars);
    // std::cout<<"h PCS open correct"<<std::endl;
    std::vector<Fr> claimedF(M,Fr(0));
    for (unsigned int i=0;i<M;i++){
        claimedF[i] = Sumcheck_f[i][0];
    }
    return std::make_tuple(true,claimedF,Sumcheck_t[0],r_Challenges2);
}

std::tuple<bool, std::vector<Fr>,Fr,std::vector<Fr>> Logup_Vector_Lookup_Int(const std::vector<std::vector<std::vector<Fr>>>& f, const std::vector<std::vector<Fr>>& t, 
    const unsigned& M, const unsigned& nVars, const unsigned& yVars,G1&G_big,G1*g_big){
    std::vector<std::vector<Fr>> fix_y_f(M,std::vector<Fr>(1u<<nVars,Fr(0)));
    std::vector<Fr> fix_y_t(1u<<nVars,Fr(0));
    std::vector<Fr> y(yVars,Fr(0));
    for (unsigned int i=0;i<yVars;i++){
        Fr y_i;y_i.setRand();
        y[i] = y_i;
    }
    for (unsigned int i=0;i<M;i++)
        for (unsigned int j=0;j<(1u<<nVars);j++)
            fix_y_f[i][j] = Int_Multi_evaluate(f[i][j],y,yVars);
    for (unsigned int i=0;i<(1u<<nVars);i++) fix_y_t[i] = Int_Multi_evaluate(t[i],y,yVars);
    std::tuple<bool,std::vector<Fr>,Fr,std::vector<Fr>> ok = Logup_Value_Lookup_Int(fix_y_f, fix_y_t, M, nVars,G_big,g_big);
    if (!std::get<0>(ok)){
        std::cout<<"Inside vector lookup: value_lookup failed"<<std::endl;
        return std::make_tuple(false,y,Fr(0),y);
    }
    std::vector<Fr> rChallenges(nVars+yVars,Fr(0));
    for (unsigned int i=0;i<yVars;i++){
        rChallenges[i] = y[i];
    }
    for (unsigned int i=0;i<nVars;i++){
        rChallenges[i+yVars] = std::get<3>(ok)[i];
    }
    return std::make_tuple(true,std::get<1>(ok),std::get<2>(ok),rChallenges);
}

std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,Fr,std::vector<Fr>> Logup_Vector_Lookup_Rational(const std::vector<std::vector<std::vector<Fr>>>& f1, const std::vector<std::vector<std::vector<Fr>>>& f2,
    const std::vector<std::vector<Fr>>& t1, const std::vector<std::vector<Fr>>& t2, const unsigned& M, const unsigned& nVars, const unsigned& yVars, G1&G_big,G1*g_big){
    std::vector<std::vector<std::vector<Fr>>> f(M, std::vector<std::vector<Fr>>(1u<<nVars,std::vector<Fr>(1u<<yVars,Fr(0))));
    std::vector<std::vector<Fr>> t(1u<<nVars,std::vector<Fr>(1u<<yVars,Fr(0)));
    // V generates a random lambda to fix two vectors into one: num + lambda*den
    Fr lambda;lambda.setRand();
    for (unsigned int i=0;i<M;i++)
        for (unsigned int j=0;j<(1u<<nVars);j++)
            for(unsigned int k=0;k<(1u<<yVars);k++){
                f[i][j][k] = f1[i][j][k] + lambda * f2[i][j][k];
            }
    for (unsigned int j=0;j<(1u<<nVars);j++)
        for(unsigned int k=0;k<(1u<<yVars);k++){
            t[j][k] = t1[j][k] + lambda * t2[j][k];
        }
    std::tuple<bool,std::vector<Fr>,Fr,std::vector<Fr>> ok = Logup_Vector_Lookup_Int(f, t, M, nVars, yVars,G_big,g_big);
    if (!std::get<0>(ok)){
        std::cout<<"Inside Rational vector lookup: Int_vector_lookup failed"<<std::endl;
        return std::make_tuple(false,std::get<3>(ok),std::get<3>(ok),Fr(0),Fr(0),std::get<3>(ok));
    }
    // P needs to claim the num and den respectively, 随机数是 std::get<3>(ok).
    std::vector<Fr> claimedf1(M,Fr(0)),claimedf2(M,Fr(0));
    Fr claimedt1,claimedt2;
    for (unsigned int i=0;i<M;i++){
        std::vector<Fr> auxi_f1(1u<<(nVars+yVars),Fr(0)),auxi_f2(1u<<(nVars+yVars),Fr(0));
        for (unsigned int j=0;j<(1u<<nVars);j++){
            for (unsigned int k=0;k<(1u<<yVars);k++){
                auxi_f1[j*(1u<<yVars)+k] = f1[i][j][k];
                auxi_f2[j*(1u<<yVars)+k] = f2[i][j][k];
            }
        }
        claimedf1[i] = Int_Multi_evaluate(auxi_f1,std::get<3>(ok),nVars+yVars);
        claimedf2[i] = Int_Multi_evaluate(auxi_f2,std::get<3>(ok),nVars+yVars);
    }
    bool flag = false;
    for (unsigned i=0;i<M;i++){
        flag = ((claimedf1[i] + lambda * claimedf2[i]) == std::get<1>(ok)[i]);
        if (!flag){
            std::cout<<"Inside Rational vector lookup: before open pcs failed"<<std::endl;
            return std::make_tuple(false,std::get<3>(ok),std::get<3>(ok),Fr(0),Fr(0),std::get<3>(ok));
        }
    }
    std::vector<Fr> auxi_t1(1u<<(nVars+yVars),Fr(0)),auxi_t2(1u<<(nVars+yVars),Fr(0));
    for (unsigned int j=0;j<(1u<<nVars);j++){
        for (unsigned int k=0;k<(1u<<yVars);k++){
            auxi_t1[j*(1u<<yVars)+k] = t1[j][k];
            auxi_t2[j*(1u<<yVars)+k] = t2[j][k];
        }
    }
    claimedt1 = Int_Multi_evaluate(auxi_t1,std::get<3>(ok),nVars+yVars);
    claimedt2 = Int_Multi_evaluate(auxi_t2,std::get<3>(ok),nVars+yVars);
    flag = ((claimedt1 + lambda * claimedt2) == std::get<2>(ok));
    if (!flag){
        std::cout<<"Inside Rational vector lookup: before open pcs failed"<<std::endl;
        return std::make_tuple(false,std::get<3>(ok),std::get<3>(ok),Fr(0),Fr(0),std::get<3>(ok));
    }
    return std::make_tuple(true,claimedf1,claimedf2,claimedt1,claimedt2,std::get<3>(ok));
}


// Sparse Commitment <-> Metadata Lookup: Row Col Value. Eq(x) Eq(y)

std::tuple<bool, Fr,Fr,Fr,std::vector<Fr>,Fr,Fr,std::vector<Fr>,Fr,Fr,std::vector<Fr>> Sparse_Commitment_Check_Int(const std::vector<Fr>& val, const std::vector<ll>& row, const std::vector<ll>& col, 
    const std::vector<Fr>& f_x, const std::vector<Fr>& f_y,
    // const MultilinearExtensionOracle_Rational& eq_x_Oracle, const MultilinearExtensionOracle_Rational& eq_y_Oracle, const MultilinearExtensionOracle_Rational& val_Oracle, 
    unsigned mVars, unsigned nVars, unsigned kVars, Fr ClaimedValue, std::vector<Fr> r1, std::vector<Fr> r2,G1&G_big,G1*g_big){
        std::tuple<bool, Fr, Fr, Fr, std::vector<Fr>> ok = Int_Sumcheck_fx_gx_hx(val,f_x,f_y,ClaimedValue,kVars);
        if (!std::get<0>(ok)){
            std::cout<<"the sparse matrix value failed"<<std::endl;
            return std::make_tuple(false,Fr(0),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok));
        }
        std::vector<Fr> eq_x_r1 = eqTable(r1,mVars);
        std::vector<Fr> eq_y_r2 = eqTable(r2,nVars);
        std::vector<std::vector<Fr>> t_x(1<<mVars, std::vector<Fr>(2,Fr(0)));
        std::vector<std::vector<Fr>> t_y(1<<nVars, std::vector<Fr>(2,Fr(0)));
        std::vector<std::vector<Fr>> f_row(1<<kVars, std::vector<Fr>(2,Fr(0)));
        std::vector<std::vector<Fr>> f_col(1<<kVars, std::vector<Fr>(2,Fr(0)));
        for (unsigned int i=0; i< (1<<mVars);i++){
            t_x[i][0] = Fr(i);
            t_x[i][1] = eq_x_r1[i];
        }
        for (unsigned int i=0; i< (1<<nVars);i++){
            t_y[i][0] = Fr(i);
            t_y[i][1] = eq_y_r2[i];
        }
        for (unsigned int i=0; i< (1<<kVars);i++){
            f_row[i][0] = Fr(row[i]);
            f_row[i][1] = f_x[i];
            f_col[i][0] = Fr(col[i]);
            f_col[i][1] = f_y[i];
        }
        unsigned int rowVars = std::max(mVars, kVars);
        unsigned int colVars = std::max(nVars, kVars);
        padVectors(t_x, 1u<<rowVars);
        padVectors(f_row, 1u<<rowVars);   
        padVectors(t_y, 1u<<colVars);
        padVectors(f_col, 1u<<colVars);    
        std::vector<std::vector<std::vector<Fr>>> f_row_extend(1,std::vector<std::vector<Fr>>(1<<rowVars, std::vector<Fr>(2,Fr(0))));
        std::vector<std::vector<std::vector<Fr>>> f_col_extend(1,std::vector<std::vector<Fr>>(1<<colVars, std::vector<Fr>(2,Fr(0))));
        f_row_extend[0] = f_row;
        f_col_extend[0] = f_col;
        // std::cout<<rowVars<<" "<<f_row.size()<<std::endl;
        // std::cout<<colVars<<" "<<f_col.size()<<std::endl;
        std::tuple<bool, std::vector<Fr>,Fr,std::vector<Fr>> ok1 = Logup_Vector_Lookup_Int(f_row_extend, t_x, 1, rowVars, 1, G_big, g_big);
        if (!std::get<0>(ok1)){
            std::cout<<"inside Sparse commitment: Vector lookup failed"<<std::endl;
            return std::make_tuple(false,Fr(0),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok));
        }
        std::vector<Fr> row_Challenges(kVars,Fr(0));
        for (unsigned int i=1;i<=kVars;i++){
            row_Challenges[i-1] = std::get<3>(ok1)[i];
        }
        Fr lambda_scalar = std::get<3>(ok1)[0];
        // P claims row(r[1:]), f_x(r[1:])
        Fr Claimedrow = Int_Multi_evaluate_ll(row,row_Challenges,kVars);
        Fr Claimedfx = Int_Multi_evaluate(f_x,row_Challenges,kVars);
        // V check its correct
        bool flag = (Claimedrow*(1-lambda_scalar) + lambda_scalar * Claimedfx) == std::get<1>(ok1)[0];
        if (!flag){
            std::cout<<"inside sparse: row pairs evaluate failed"<<std::endl;
            return std::make_tuple(false,Fr(0),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok));
        }
        std::vector<Fr> col_Challenges(kVars,Fr(0));
        std::tuple<bool, std::vector<Fr>,Fr,std::vector<Fr>> ok2 = Logup_Vector_Lookup_Int(f_col_extend, t_y, 1, colVars, 1, G_big, g_big);
        if (!std::get<0>(ok2)){
            std::cout<<"inside Sparse commitment: Vector lookup failed"<<std::endl;
            return std::make_tuple(false,Fr(0),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok));
        }
        for (unsigned int i=1;i<=kVars;i++){
            col_Challenges[i-1] = std::get<3>(ok2)[i];
        }
        lambda_scalar = std::get<3>(ok2)[0];
        Fr Claimedcol= Int_Multi_evaluate_ll(col,col_Challenges,kVars);
        Fr Claimedfy = Int_Multi_evaluate(f_y,col_Challenges,kVars);
        flag = (Claimedcol*(1-lambda_scalar) + lambda_scalar * Claimedfy) == std::get<1>(ok2)[0];
        if (!flag){
            std::cout<<"inside sparse: col pairs evaluate failed"<<std::endl;
            return std::make_tuple(false,Fr(0),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok),Fr(0),Fr(0),std::get<4>(ok));
        }
        return std::make_tuple(true,std::get<1>(ok),std::get<2>(ok),std::get<3>(ok),std::get<4>(ok),Claimedrow,Claimedfx,row_Challenges,Claimedcol,Claimedfy,col_Challenges);
}


vector<Fr> buildNegRange(const int& nVars) {
    const int range = 1 << nVars;
    vector<Fr> negRange;
    negRange.reserve(range);

    for (int i = 0; i < range; i++) {
        Fr tmp = Fr(i);    
        negRange.push_back(-tmp);
    }
    return negRange;
}

vector<Fr> buildPosRange(const int& nVars) {
    const int range = 1 << nVars;
    vector<Fr> negRange;
    negRange.reserve(range);

    for (int i = 0; i < range; i++) {
        Fr tmp = Fr(i);    
        negRange.push_back(tmp);
    }
    return negRange;
}


void padValues(std::vector<std::vector<Fr>>& mat, size_t nVars) {
    size_t targetLen = 1u << nVars;

    for (auto& row : mat) {
        if (row.empty()) continue; 
        Fr last = row.back();
        while (row.size() < targetLen) {
            row.push_back(last);
        }
    }
}


std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> Logup_Value_Lookup_Int_not_equal_length(const std::vector<std::vector<Fr>>& f, const std::vector<Fr>& t, const unsigned& M, 
    const unsigned& fVars,const unsigned& nVars, G1&G,G1*g_big){
    std::unordered_map<Fr, std::size_t> dict_f;
    dict_f.reserve(1u << fVars);
    for (const auto& fi : f) {
        for (const auto& val : fi) {
            ++dict_f[val];  
        }
    }
    std::unordered_map<Fr, std::size_t> dict_t;
    dict_t.reserve(1u << nVars);
    for (const auto& val : t) {
        ++dict_t[val];
    }

    const std::size_t size_m = (1u << nVars); 
    std::vector<Fr> m(size_m, Fr(0));    

    for (std::size_t i = 0; i < size_m; ++i) {
        const Fr& key = t[i];
        
        auto itF = dict_f.find(key);
        auto itT = dict_t.find(key);
        if (itF == dict_f.end() || itT == dict_t.end() || itT->second == 0) {
            m[i] = Fr(0);
        } else {
            Fr numerator   = Fr(itF->second);  
            Fr denominator = Fr(itT->second);
            Fr invDen;
            Fr::inv(invDen, denominator);     
            m[i] = numerator * invDen;               
        }
    }
    G1* commitM = prover_commit_Fr(m.data(),g_big,nVars,16);
    // std::cout<<"m commit success"<<std::endl;
    // V sends a random field x
    Fr x; x.setRand();
    // P computes M MLE polynomials g1,g2,...,gM 1/(x+f_i(x)) and 1 MLE poly h(x) = m(x)/(x+t(x)) on hypercube 2^nVars
    std::vector<std::vector<Fr>> g(M, std::vector<Fr>(1u<<fVars, Fr(0)));
    std::vector<Fr> h(1u<<nVars, Fr(0));
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<fVars); j++){
            g[i][j] = Fr(1) / (x + f[i][j]);
        }
    }
    for(unsigned int j=0; j<(1u<<nVars); j++){
        h[j] = m[j] / (x + t[j]);
    }
    // P sends all the oracle of g1,g2,...,gM,h to V
    std::vector<G1*> commitg(M);
    for (unsigned int i=0;i<M;i++){
        commitg[i] = prover_commit_Fr(g[i].data(),g_big,fVars,16);
    }
    G1* commitH = prover_commit_Fr(h.data(),g_big,nVars,16);
    std::vector<Fr> Q1(1u<<fVars, Fr(0));
    std::vector<Fr> Q2(1u<<nVars, Fr(0));
    
    for(unsigned int i=0; i<M; i++){
        for(unsigned int j=0; j<(1u<<fVars); j++){
            Q1[j] = Q1[j] + g[i][j];
        }
    }
    Q2 = h;
    Fr Claimed_Sum = Fr(0);
    Fr Claimed_Sum2 = Fr(0);
    for (unsigned int i=0;i<(1u<<fVars);i++){
        Claimed_Sum = Claimed_Sum + Q1[i];
    }
    Claimed_Sum2 = Claimed_Sum;
    // ΣQ1 = sum
    Fr point0, point1;
    bool ok = false;
    point0 = Fr(0);
    point1 = Fr(0);
    std::vector<Fr> r_Challenges_Q1(fVars,Fr(0));
    for(unsigned int i=0; i<fVars; i++){
        // P computes 2 points and sends them to V
        point0 = Fr(0);
        point1 = Fr(0);
        for(unsigned int j=0; j<(1u<<(fVars-1-i)); j++){
            point0 = point0 + Q1[2*j];
            point1 = point1 + Q1[2*j+1];
        }
        // V checks 2 points sum = claimed_sum
        ok = (point0+point1 == Claimed_Sum);
        if (!ok){
            cout<<"sigma_g failed"<<endl;
            return std::make_tuple(false,r_Challenges_Q1,r_Challenges_Q1,Fr(0),r_Challenges_Q1);
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges_Q1[i] = r_i;
        Claimed_Sum = r_i * point1 + (1-r_i)*point0;
        // P maintains bkp table
        Q1 = Int_ri_Table_Compute_fx(fVars-i,Q1,r_i);
    }
    // ΣQ2 = sum
    ok = false;
    point0 = Fr(0);
    point1 = Fr(0);
    std::vector<Fr> r_Challenges_Q2(nVars,Fr(0));
    for(unsigned int i=0; i<nVars; i++){
        // P computes 2 points and sends them to V
        point0 = Fr(0);
        point1 = Fr(0);
        for(unsigned int j=0; j<(1u<<(nVars-1-i)); j++){
            point0 = point0 + Q2[2*j];
            point1 = point1 + Q2[2*j+1];
        }
        // V checks 2 points sum = claimed_sum
        ok = (point0+point1 == Claimed_Sum2);
        if (!ok){
            cout<<"sigma_h failed"<<endl;
            return std::make_tuple(false,r_Challenges_Q1,r_Challenges_Q1,Fr(0),r_Challenges_Q1);
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges_Q2[i] = r_i;
        Claimed_Sum2 = r_i * point1 + (1-r_i)*point0;
        // P maintains bkp table
        Q2 = Int_ri_Table_Compute_fx(nVars-i,Q2,r_i);
    }
    std::vector<Fr> Claimedg(M,Fr(0));
    for (unsigned int i=0;i<M;i++){
        Claimedg[i] = Int_Multi_evaluate(g[i],r_Challenges_Q1,fVars);
    }
    Fr check_g_sum=Fr(0);
    for (unsigned int i=0;i<M;i++){
        check_g_sum = check_g_sum + Claimedg[i];
    }
    ok = (check_g_sum == Claimed_Sum);
    if(!ok) {
        std::cout<<"sigma_g last round failed"<<std::endl;
        return std::make_tuple(false,r_Challenges_Q1,r_Challenges_Q1,Fr(0),r_Challenges_Q1);
    }

    for (unsigned int i=0;i<M;i++){
        // std::cout<<i<<std::endl;
        openCommit(g[i],r_Challenges_Q1.data(),Claimedg[i],G,g_big,commitg[i],fVars);
    }
    // std::cout<<"g open"<<std::endl;
    openCommit(h,r_Challenges_Q2.data(),Claimed_Sum2,G,g_big,commitH,nVars);
    std::vector<Fr> rg = RandomFieldChallenge_Generator(fVars);
    std::vector<Fr> rh = RandomFieldChallenge_Generator(nVars);
    std::vector<Fr> random_lambda_scalar = RandomFieldChallenge_Generator(M);
    std::vector<Fr> eq_g(1u<<fVars,Fr(1));    
    for (std::size_t i = 0; i < (1u<<fVars); i++) {
        std::vector<int> index(fVars);
        index = indexToBits(i,fVars);
        for (std::size_t j = 0; j < fVars; j++) {
            Fr term1 = rg[j] * Fr(index[j]);         // e_i * x_i
            Fr term2 = (Fr(1) - rg[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
        eq_g[i] = eq_g[i] * (term1 + term2);
        }
    }
    int max_degree = 3;
    Claimed_Sum = Fr(0);
    std::vector<Fr> r_Challenges_g(fVars,Fr(0));
    std::vector<std::vector<Fr>> Sumcheck_f = f;
    std::vector<std::vector<Fr>> Sumcheck_g = g;
    std::vector<Fr> Sumcheck_eq = eq_g;
    for(unsigned int i=0; i<fVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<std::vector<Fr>>> Auxiliary_f(max_degree+1, std::vector<std::vector<Fr>>(M, std::vector<Fr>(1<<(fVars-1-i),Fr(0))));
        std::vector<std::vector<std::vector<Fr>>> Auxiliary_g(max_degree+1, std::vector<std::vector<Fr>>(M, std::vector<Fr>(1<<(fVars-1-i),Fr(0))));
        // std::cout<<"Auxiliary_f init done"<<std::endl;
        for (unsigned jj=0;jj<M;jj++){
            for (unsigned kk=0;kk<(1u<<(fVars-1-i));kk++){
                Auxiliary_f[0][jj][kk] = Sumcheck_f[jj][kk*2];
                Auxiliary_f[1][jj][kk] = Sumcheck_f[jj][kk*2+1];
                Auxiliary_g[0][jj][kk] = Sumcheck_g[jj][kk*2];
                Auxiliary_g[1][jj][kk] = Sumcheck_g[jj][kk*2+1];
            }
        }
        for (unsigned j=2;j<max_degree+1;j++){
            for (unsigned jj=0;jj<M;jj++){
                Auxiliary_f[j][jj] = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_f[jj], Fr(j));
                Auxiliary_g[j][jj] = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_g[jj], Fr(j));
            }
        }
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(fVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(fVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_eq, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(fVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(fVars-1-i)); jj++){
                for(unsigned int kk=0; kk<M; kk++){
                    result[j][jj] = result[j][jj] + Auxiliary_eq[j][jj] * random_lambda_scalar[kk] * (Auxiliary_g[j][kk][jj]*(x+Auxiliary_f[j][kk][jj])-Fr(1));
                }
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(fVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok){
            cout<<"all g failed"<<endl;
            return std::make_tuple(false,r_Challenges_Q1,r_Challenges_Q1,Fr(0),r_Challenges_Q1);
        }
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges_g[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        for (unsigned jj=0;jj<M;jj++){
            Sumcheck_f[jj] = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_f[jj], r_i);
            Sumcheck_g[jj] = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_g[jj], r_i);
        }
        Sumcheck_eq = Int_ri_Table_Compute_fx(fVars-i, Sumcheck_eq, r_i);
    }
    Fr checker_g = Fr(0);
    for (unsigned int i=0;i<M;i++){
        checker_g = checker_g + Sumcheck_eq[0] * random_lambda_scalar[i] * (Sumcheck_g[i][0]*(x+Sumcheck_f[i][0])-Fr(1));
    }
    ok = (checker_g == Claimed_Sum);
    if (!ok) {
        std::cout<<"all g's last round claim failed"<<std::endl;
        return std::make_tuple(false,r_Challenges_g,r_Challenges_g,Fr(0),r_Challenges_g);
    }
    // std::cout<<"all g's last round claim passed"<<std::endl;
    // P runs sumcheck to prove h
    std::vector<Fr> eq_h(1u<<nVars,Fr(1));    
    for (std::size_t i = 0; i < (1u<<nVars); i++) {
        std::vector<int> index(nVars);
        index = indexToBits(i,nVars);
        for (std::size_t j = 0; j < nVars; j++) {
            Fr term1 = rh[j] * Fr(index[j]);         // e_i * x_i
            Fr term2 = (Fr(1) - rh[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
        eq_h[i] = eq_h[i] * (term1 + term2);
        }
    }
    for (unsigned int i=0;i<M;i++){
        openCommit(g[i],r_Challenges_g.data(),Sumcheck_g[i][0],G,g_big,commitg[i],fVars);
    }
    // std::cout<<"all the g PCS open correct"<<std::endl;
    std::vector<Fr> claimedF(M,Fr(0));
    for (unsigned int i=0;i<M;i++){
        claimedF[i] = Sumcheck_f[i][0];
    }
    // P runs sumcheck with V
    Claimed_Sum = Fr(0);
    std::vector<Fr> r_Challenges_h(nVars,Fr(0));
    std::vector<Fr> Sumcheck_t = t;
    std::vector<Fr> Sumcheck_h = h;
    std::vector<Fr> Sumcheck_m = m;
    Sumcheck_eq = eq_h;
    for(unsigned int i=0; i<nVars; i++){
        // P computes max_degree+1 points and sends them to V
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
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_h[j][jj]*(x+Auxiliary_t[j][jj])-Auxiliary_m[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(nVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        ok = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!ok){
            cout<<"h correctness failed"<<endl;
            return std::make_tuple(false,r_Challenges_g,r_Challenges_g,Fr(0),r_Challenges_g);
        } 
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges_h[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_t = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_t, r_i);
        Sumcheck_eq = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_eq, r_i);
        Sumcheck_m = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_m, r_i);
        Sumcheck_h = Int_ri_Table_Compute_fx(nVars-i, Sumcheck_h, r_i);
    }
    ok = ((Sumcheck_eq[0] * (Sumcheck_h[0]*(x+Sumcheck_t[0])-Sumcheck_m[0])) == Claimed_Sum);
    if (!ok) {
        std::cout<<"h's last round claim failed"<<std::endl;
        return std::make_tuple(false,r_Challenges_h,r_Challenges_h,Fr(0),r_Challenges_h);
    }
    openCommit(m,r_Challenges_h.data(),Sumcheck_m[0],G,g_big,commitM,nVars);
    openCommit(h,r_Challenges_h.data(),Sumcheck_h[0],G,g_big,commitH,nVars);
    return std::make_tuple(true,claimedF,r_Challenges_g,Sumcheck_t[0],r_Challenges_h);
}



std::tuple<bool, std::vector<Fr>,std::vector<Fr>, Fr,std::vector<Fr>> Int_Range_Proof(const std::vector<std::vector<Fr>>& f, const std::vector<Fr>& t, const unsigned int& M, const unsigned int& nVars,
    const unsigned int& Nega_size,G1&G_big,G1*g_big){
    std::vector<std::vector<Fr>> A = f;
    // padValues(A,Nega_size);
    std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok = Logup_Value_Lookup_Int_not_equal_length(A,t,M,nVars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok)){
        cout<<"Inside int range proof: lookup failed!"<<endl;
        return std::tuple(false,std::get<2>(ok),std::get<2>(ok),Fr(0),std::get<4>(ok));
    }
    return std::tuple(true,std::get<1>(ok),std::get<2>(ok),std::get<3>(ok),std::get<4>(ok));
}


std::tuple<bool, std::vector<Fr>,std::vector<Fr>, Fr,std::vector<Fr>> Int_Range_Proof_Lasso(const std::vector<std::vector<Fr>>& f, const std::vector<Fr>& t, const unsigned int& M, 
    const unsigned int& nVars, const unsigned int& Nega_size,G1&G_big,G1*g_big){
    std::vector<std::vector<Fr>> A = f;
    
    std::vector<std::vector<Fr>> f1(M,std::vector<Fr>(1u<<nVars,Fr(0)));
    std::vector<std::vector<Fr>> f2(M,std::vector<Fr>(1u<<nVars,Fr(0)));
    for (unsigned int i=0;i<M;i++){
        for (unsigned int j=0;j<(1u<<nVars);j++){
            char buf[256];
            A[i][j].getStr(buf, sizeof(buf));
            std::string s(buf);
        
            // cout<<s<<endl;
            long long value = std::stoll(s);
            long long divisor = 1LL << Nega_size;
            f2[i][j] = Fr(value >> Nega_size);
            f1[i][j] = Fr(value & (divisor - 1));
        }
    }
    vector<G1*> commitf1(M);
    vector<G1*> commitf2(M);
    for (unsigned int i=0;i<M;i++){
        commitf1[i] = prover_commit_Fr(f1[i].data(),g_big,nVars,16);
        commitf2[i] = prover_commit_Fr(f2[i].data(),g_big,nVars,16);
    }


    std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok1 = Logup_Value_Lookup_Int_not_equal_length(f1,t,M,nVars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok1)){
        cout<<"Inside int range proof: f1 lookup failed!"<<endl;
        return std::tuple(false,std::get<2>(ok1),std::get<2>(ok1),Fr(0),std::get<4>(ok1));
    }
    for (unsigned int i=0;i<M;i++){
        openCommit(f1[i],std::get<2>(ok1).data(),std::get<1>(ok1)[i],G_big,g_big,commitf1[i],nVars);
    }

    std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok2 = Logup_Value_Lookup_Int_not_equal_length(f2,t,M,nVars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok2)){
        cout<<"Inside int range proof: f2 lookup failed!"<<endl;
        return std::tuple(false,std::get<2>(ok2),std::get<2>(ok2),Fr(0),std::get<4>(ok2));
    }
    for (unsigned int i=0;i<M;i++){
        openCommit(f2[i],std::get<2>(ok2).data(),std::get<1>(ok2)[i],G_big,g_big,commitf2[i],nVars);
    }

    vector<Fr> rChallenges = std::get<2>(ok1);
    vector<Fr> Claimedf(M,Fr(0));
    vector<Fr> Claimedf2(M,Fr(0));
    for (unsigned int i=0;i<M;i++){
        Claimedf[i] = Int_Multi_evaluate(A[i],rChallenges,nVars);
        Claimedf2[i] = Int_Multi_evaluate(f2[i],rChallenges,nVars);
        if (!(Claimedf2[i] * Fr(1u<<Nega_size) + std::get<1>(ok1)[i] == Claimedf[i])){
            cout<<"table defactorization failed"<<endl;
            return std::tuple(false,std::get<2>(ok1),std::get<2>(ok1),Fr(0),std::get<4>(ok1));
        }
        openCommit(f2[i],rChallenges.data(),Claimedf2[i],G_big,g_big,commitf2[i],nVars);
    }

    return std::tuple(true,Claimedf,rChallenges,std::get<3>(ok1),std::get<4>(ok1));
}

std::tuple<bool, Fr,Fr, Fr,Fr,std::vector<Fr>,Fr,std::vector<Fr>> Rational_Range_Proof(const std::vector<Fr>& p, const std::vector<Fr>& q, 
    const std::vector<Fr>& a, const std::vector<Fr>& b, const std::vector<Fr>& t, const unsigned int& nVars,const unsigned int& Nega_size,G1&G_big,G1*g_big){
    std::vector<Fr> Q(1u<<nVars,Fr(0));
    for (unsigned int i=0;i<(1u<<nVars);i++){
        Q[i] = p[i]*b[i]-q[i]*a[i];
    }
    std::vector<std::vector<Fr>> Q_matrix(1,std::vector<Fr>(1u<<nVars,Fr(0)));
    Q_matrix[0] = Q;
    // std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok = Int_Range_Proof(Q_matrix,t,1,nVars,Nega_size,G_big,g_big);
    std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok = Int_Range_Proof_Lasso(Q_matrix,t,1,nVars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok)){
        cout<<"Inside Rational Range proof: Int_Range_Proof failed"<<endl;
        return std::make_tuple(false, Fr(0), Fr(0), Fr(0), Fr(0), std::get<4>(ok),std::get<3>(ok),std::get<4>(ok));
    }
    std::vector<Fr> r1(nVars,Fr(0));
    r1 = std::get<2>(ok);
    std::vector<Fr> eq(1u<<nVars, Fr(1));
    for (std::size_t i = 0; i < (1u<<nVars); i++) {
        std::vector<int> index(nVars);
        index = indexToBits(i,nVars);
        for (std::size_t j = 0; j < nVars; j++) {
            Fr term1 = r1[j] * Fr(index[j]);         // e_i * x_i
            Fr term2 = (Fr(1) - r1[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
            eq[i] = eq[i] * (term1 + term2);
        }
    }
    // P claims ClaimedValue
    Fr Claimed_Sum = std::get<1>(ok)[0];
    // P computes 4 points and sends them to V
    int max_degree = 3;
    bool flag = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(nVars,Fr(0));
    std::vector<Fr> Sumcheck_eq = eq;
    std::vector<Fr> Sumcheck_p = p;
    std::vector<Fr> Sumcheck_q = q;
    std::vector<Fr> Sumcheck_a = a;
    std::vector<Fr> Sumcheck_b = b;
    int kVars = nVars;
    for(unsigned int i=0; i<nVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_p(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_q(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_p[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_p, Fr(j));
            Auxiliary_q[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_q, Fr(j));
            Auxiliary_a[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a, Fr(j));
            Auxiliary_b[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_p[0][kk] = Sumcheck_p[kk*2];
            Auxiliary_p[1][kk] = Sumcheck_p[kk*2+1];
            Auxiliary_q[0][kk] = Sumcheck_q[kk*2];
            Auxiliary_q[1][kk] = Sumcheck_q[kk*2+1];
            Auxiliary_a[0][kk] = Sumcheck_a[kk*2];
            Auxiliary_a[1][kk] = Sumcheck_a[kk*2+1];
            Auxiliary_b[0][kk] = Sumcheck_b[kk*2];
            Auxiliary_b[1][kk] = Sumcheck_b[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_p[j][jj]* Auxiliary_b[j][jj] - Auxiliary_q[j][jj]* Auxiliary_a[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        flag = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!flag) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
        Sumcheck_p = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_p, r_i);
        Sumcheck_q = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_q, r_i);
        Sumcheck_a = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a, r_i);
        Sumcheck_b = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b, r_i);
    }
    if (!flag) {
        std::cout<<"Designed Sumcheck failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), Fr(0), Fr(0), Fr(0), r_Challenges,std::get<3>(ok),std::get<4>(ok));
    }
    flag == ((Sumcheck_eq[0]*(Sumcheck_p[0]*Sumcheck_b[0] - Sumcheck_q[0]*Sumcheck_a[0])) == Claimed_Sum);
    return std::make_tuple(flag, Sumcheck_p[0], Sumcheck_q[0], Sumcheck_a[0], Sumcheck_b[0], r_Challenges,std::get<3>(ok),std::get<4>(ok));
}

std::tuple<bool, Fr,Fr, Fr,Fr,std::vector<Fr>,Fr,std::vector<Fr>> Rational_Range_Proof_Lasso(const std::vector<Fr>& p, const std::vector<Fr>& q, 
    const std::vector<Fr>& a, const std::vector<Fr>& b, const std::vector<Fr>& t, const unsigned int& nVars,const unsigned int& Nega_size,G1&G_big,G1*g_big){
    std::vector<Fr> Q(1u<<nVars,Fr(0));
    for (unsigned int i=0;i<(1u<<nVars);i++){
        Q[i] = q[i]*a[i] - p[i]*b[i];
    }
    std::vector<std::vector<Fr>> Q_matrix(1,std::vector<Fr>(1u<<nVars,Fr(0)));
    Q_matrix[0] = Q;
    // std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok = Int_Range_Proof(Q_matrix,t,1,nVars,Nega_size,G_big,g_big);
    std::tuple<bool, std::vector<Fr>,std::vector<Fr>,Fr,std::vector<Fr>> ok = Int_Range_Proof_Lasso(Q_matrix,t,1,nVars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok)){
        cout<<"Inside Rational Range proof: Int_Range_Proof failed"<<endl;
        return std::make_tuple(false, Fr(0), Fr(0), Fr(0), Fr(0), std::get<4>(ok),std::get<3>(ok),std::get<4>(ok));
    }
    std::vector<Fr> r1(nVars,Fr(0));
    r1 = std::get<2>(ok);
    // for (unsigned int i=0;i<nVars;i++){
    //     r1[i] = std::get<3>(ok)[i];
    // }
    std::vector<Fr> eq(1u<<nVars, Fr(1));
    for (std::size_t i = 0; i < (1u<<nVars); i++) {
        std::vector<int> index(nVars);
        index = indexToBits(i,nVars);
        for (std::size_t j = 0; j < nVars; j++) {
            Fr term1 = r1[j] * Fr(index[j]);         // e_i * x_i
            Fr term2 = (Fr(1) - r1[j]) * Fr(1 - index[j]); // (1 - e_i) * (1 - x_i)
            eq[i] = eq[i] * (term1 + term2);
        }
        // std::cout<<i<<" "<<index[0]<<index[1]<<" "<<eq0[i]<<std::endl;
    }
    // P claims ClaimedValue
    Fr Claimed_Sum = std::get<1>(ok)[0];
    // P computes 4 points and sends them to V
    int max_degree = 3;
    bool flag = false;
    std::vector<Fr> points(max_degree+1,Fr(0));
    std::vector<Fr> r_Challenges(nVars,Fr(0));
    std::vector<Fr> Sumcheck_eq = eq;
    std::vector<Fr> Sumcheck_p = p;
    std::vector<Fr> Sumcheck_q = q;
    std::vector<Fr> Sumcheck_a = a;
    std::vector<Fr> Sumcheck_b = b;
    int kVars = nVars;
    for(unsigned int i=0; i<nVars; i++){
        // P computes max_degree+1 points and sends them to V
        std::vector<std::vector<Fr>> Auxiliary_eq(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_p(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_q(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_a(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> Auxiliary_b(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<std::vector<Fr>> result(max_degree+1, std::vector<Fr>(1<<(kVars-1-i),Fr(0)));
        std::vector<Fr> result_sum(max_degree+1, Fr(0));
        for (unsigned j=2;j<max_degree+1;j++){
            Auxiliary_eq[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, Fr(j));
            Auxiliary_p[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_p, Fr(j));
            Auxiliary_q[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_q, Fr(j));
            Auxiliary_a[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a, Fr(j));
            Auxiliary_b[j] = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b, Fr(j));
        }
        for (unsigned kk=0;kk<(1u<<(kVars-1-i));kk++){
            Auxiliary_eq[0][kk] = Sumcheck_eq[kk*2];
            Auxiliary_eq[1][kk] = Sumcheck_eq[kk*2+1];
            Auxiliary_p[0][kk] = Sumcheck_p[kk*2];
            Auxiliary_p[1][kk] = Sumcheck_p[kk*2+1];
            Auxiliary_q[0][kk] = Sumcheck_q[kk*2];
            Auxiliary_q[1][kk] = Sumcheck_q[kk*2+1];
            Auxiliary_a[0][kk] = Sumcheck_a[kk*2];
            Auxiliary_a[1][kk] = Sumcheck_a[kk*2+1];
            Auxiliary_b[0][kk] = Sumcheck_b[kk*2];
            Auxiliary_b[1][kk] = Sumcheck_b[kk*2+1];
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result[j][jj] = Auxiliary_eq[j][jj] * (Auxiliary_q[j][jj]* Auxiliary_a[j][jj] - Auxiliary_p[j][jj]* Auxiliary_b[j][jj]);
            }
        }
        for(unsigned int j=0; j<max_degree+1; j++){
            for(unsigned int jj=0; jj<(1u<<(kVars-1-i)); jj++){
                result_sum[j] = result_sum[j] + result[j][jj];
            }
        }
        // V checks 2 points sum = claimed_sum
        flag = (result_sum[0] + result_sum[1] == Claimed_Sum);
        if (!flag) break;
        // V generates random r_i and sends it to P. V computes next Claimed_Sum.
        Fr r_i;r_i.setRand();
        r_Challenges[i] = r_i;
        Claimed_Sum = Int_lagrangeInterpolation(result_sum,r_i,max_degree);
        // P maintains bkp table
        Sumcheck_eq = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_eq, r_i);
        Sumcheck_p = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_p, r_i);
        Sumcheck_q = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_q, r_i);
        Sumcheck_a = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_a, r_i);
        Sumcheck_b = Int_ri_Table_Compute_fx(kVars-i, Sumcheck_b, r_i);
    }
    if (!flag) {
        std::cout<<"Designed Sumcheck failed!"<<std::endl;
        return std::make_tuple(false, Fr(0), Fr(0), Fr(0), Fr(0), r_Challenges,std::get<3>(ok),std::get<4>(ok));
    }
    flag == ((Sumcheck_q[0]*Sumcheck_a[0] - Sumcheck_eq[0]*(Sumcheck_p[0]*Sumcheck_b[0])) == Claimed_Sum);
    return std::make_tuple(flag, Sumcheck_p[0], Sumcheck_q[0], Sumcheck_a[0], Sumcheck_b[0], r_Challenges,std::get<3>(ok),std::get<4>(ok));
}