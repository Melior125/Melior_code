#include <bits/stdc++.h>
#include "SetMembership_Multi.cpp"

#include <vector>
#include <cstddef> // for size_t
#include <cassert>
using namespace std;

template<typename T>
std::vector<T> transpose_power2_matrix(const std::vector<T>& A, unsigned int m_vars, unsigned int n_vars) {
    size_t rows = 1u << n_vars;
    size_t cols = 1u << m_vars;
    assert(A.size() == rows * cols);

    std::vector<T> A_transposed(A.size());

    for (size_t i = 0; i < rows; ++i) {
        for (size_t j = 0; j < cols; ++j) {
            A_transposed[i * cols + j] = A[j * rows + i];
        }
    }

    return A_transposed;
}

template<typename T>
std::vector<T> transpose_concat(const std::vector<T>& r, unsigned int d_vars, unsigned int N_vars) {
    assert(r.size() == d_vars + N_vars);
    std::vector<T> result(d_vars + N_vars);


    for (unsigned int i = 0; i < N_vars; ++i) {
        result[i] = r[d_vars + i];
    }


    for (unsigned int i = 0; i < d_vars; ++i) {
        result[N_vars + i] = r[i];
    }

    return result;
}


Rational_Fr parseFraction(const string &s) {
    Rational_Fr res;
    auto pos = s.find('/');
    if (pos == string::npos) {
        // res.numerator = Fr(stoll(s));
        res.numerator.setStr(s, 10);
        res.denominator = Fr(1);
    } else {
        // res.numerator = Fr(stoll(s.substr(0, pos)));
        res.numerator.setStr(s.substr(0, pos), 10);
        res.denominator.setStr(s.substr(pos + 1));
    }
    return res;
}

std::pair<ll,ll> parseFraction_ll(const string &s) {
    ll num, den;
    auto pos = s.find('/');
    if (pos == string::npos) {
        num = stoll(s);
        den = 1;
    } else {
        num = stoll(s.substr(0, pos));
        den = stoll(s.substr(pos + 1));
    }
    return std::make_pair(num,den);
}

int nextPowerOfTwoExponent(int x) {
    if (x == 0) return 0;

    x--;
    int exp = 0;
    while (x > 0) {
        x >>= 1;
        ++exp;
    }
    return exp;
}

int main(int argc, char* argv[]) 
{
    if (argc < 2) {
        cerr << "Usage: " << argv[0] << " <input_file>\n";
        return 1;
    }

    initPairing(mcl::BN254);
    const int l_big = 32;

    G1 g_big[1 << (l_big / 2)];
    G1 G_big = gen_gi(g_big, 1 << (l_big - l_big / 2));

    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    ifstream fin(argv[1]);
    if (!fin.is_open()) {
        cerr << "Cannot open " << argv[1] << '\n';
        return 1;
    }
    timer t(true);
    int communication = 0;
    string header;
    getline(fin, header); 
    int m, d;
    fin >> m >> d; 
    vector<vector<Rational_Fr>> A(m, vector<Rational_Fr>(d));
    int m_pad_vars, d_pad_vars;
    m_pad_vars = nextPowerOfTwoExponent(m);
    d_pad_vars = nextPowerOfTwoExponent(d);
    // ll* A_num = new ll[1<<(m_pad_vars+d_pad_vars)]();
    // ll* A_den = new ll[1<<(m_pad_vars+d_pad_vars)]();
    // ll* b_num = new ll[1<<m_pad_vars]();
    // ll* b_den = new ll[1<<m_pad_vars]();
    // ll* c_num = new ll[1<<d_pad_vars]();
    // ll* c_den = new ll[1<<d_pad_vars]();
    std::vector<Fr> A_num_Fr(1 << (m_pad_vars + d_pad_vars), Fr(0));
    std::vector<Fr> A_den_Fr(1 << (m_pad_vars + d_pad_vars), Fr(1));
    std::vector<Fr> b_num_Fr(1 << m_pad_vars, Fr(0));
    std::vector<Fr> b_den_Fr(1 << m_pad_vars, Fr(1));
    std::vector<Fr> c_num_Fr(1 << d_pad_vars, Fr(0));
    std::vector<Fr> c_den_Fr(1 << d_pad_vars, Fr(1));


    for (int i = 0; i < m; i++){
        for (int j = 0; j < d; j++){
            string fracStr;
            fin >> fracStr;
            A[i][j] = parseFraction(fracStr);
            A_num_Fr[i*(1<<d_pad_vars)+j] = A[i][j].numerator;
            A_den_Fr[i*(1<<d_pad_vars)+j] = A[i][j].denominator;
            // auto parse_result = parseFraction_ll(fracStr);
            // A_num[i*(1<<d_pad_vars)+j] = parse_result.first;
            // A_den[i*(1<<d_pad_vars)+j] = parse_result.second;
            // A_num_Fr[i*(1<<d_pad_vars)+j] = Fr(A_num[i*(1<<d_pad_vars)+j]);
            // A_den_Fr[i*(1<<d_pad_vars)+j] = Fr(A_den[i*(1<<d_pad_vars)+j]);
        }
    }
    getline(fin, header); 
    getline(fin, header); 
    vector<Rational_Fr> b(m);
    for (int i = 0; i < m; i++){
        string fracStr;
        fin >> fracStr;
        b[i] = parseFraction(fracStr);
        b_num_Fr[i] = b[i].numerator;
        b_den_Fr[i] = b[i].denominator; 
        // auto parse_result = parseFraction_ll(fracStr);
        // b_num[i] = parse_result.first;
        // b_den[i] = parse_result.second;
        // b_num_Fr[i] = Fr(b_num[i]);
        // b_den_Fr[i] = Fr(b_den[i]);
    }
    getline(fin, header);
    getline(fin, header);
    vector<Rational_Fr> c(d);
    for (int j = 0; j < d; j++){
        string fracStr;
        fin >> fracStr;
        c[j] = parseFraction(fracStr);
        c_num_Fr[j] = c[j].numerator;
        c_den_Fr[j] = c[j].denominator;
        // auto parse_result = parseFraction_ll(fracStr);
        // c_num[j] = parse_result.first;
        // c_den[j] = parse_result.second;
        // c_num_Fr[j] = Fr(c_num[j]);
        // c_den_Fr[j] = Fr(c_den[j]);
    }
    

    getline(fin, header);
    getline(fin, header);
    

    int N, n;
    fin >> N >> n >> d >> m; 
    int best_node;
    fin >> best_node;      
    int N_pad_vars, n_pad_vars, dd_plus_m_pad_vars;
    N_pad_vars = nextPowerOfTwoExponent(N);
    n_pad_vars = nextPowerOfTwoExponent(n);
    dd_plus_m_pad_vars = nextPowerOfTwoExponent(m+2*d);
    // ll* X_num = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* X_den = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* L_list_num = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* L_list_den = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* R_list_num = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* R_list_den = new ll[1<<(N_pad_vars+d_pad_vars)]();
    // ll* Y_list_num = new ll[1<<(N_pad_vars+dd_plus_m_pad_vars)]();
    // ll* Y_list_den = new ll[1<<(N_pad_vars+dd_plus_m_pad_vars)]();
    // ll* eta_list_num = new ll[1<<n_pad_vars]();
    // ll* eta_list_den = new ll[1<<n_pad_vars]();
    // ll* V_list_num = new ll[1<<N_pad_vars]();
    // ll* V_list_den = new ll[1<<N_pad_vars]();
    // ll* T_list_ll = new ll[1<<(N_pad_vars+d_pad_vars)]();
    std::vector<Fr> X_num_Fr(1 << (N_pad_vars + d_pad_vars), Fr(0));
    std::vector<Fr> X_den_Fr(1 << (N_pad_vars + d_pad_vars), Fr(1));
    std::vector<Fr> L_list_num_Fr(1 << (N_pad_vars + d_pad_vars), Fr(0));
    std::vector<Fr> L_list_den_Fr(1 << (N_pad_vars + d_pad_vars), Fr(1));
    std::vector<Fr> R_list_num_Fr(1 << (N_pad_vars + d_pad_vars), Fr(0));
    std::vector<Fr> R_list_den_Fr(1 << (N_pad_vars + d_pad_vars), Fr(1));
    std::vector<Fr> Y_list_num_Fr(1 << (N_pad_vars + dd_plus_m_pad_vars), Fr(0));
    std::vector<Fr> Y_list_den_Fr(1 << (N_pad_vars + dd_plus_m_pad_vars), Fr(1));
    std::vector<Fr> eta_list_num_Fr(1 << n_pad_vars, Fr(0));
    std::vector<Fr> eta_list_den_Fr(1 << n_pad_vars, Fr(1));
    std::vector<Fr> V_list_num_Fr(1 << N_pad_vars, Fr(0));
    std::vector<Fr> V_list_den_Fr(1 << N_pad_vars, Fr(1));
    std::vector<Fr> T_list_Fr(1 << (n_pad_vars + d_pad_vars), Fr(0));
    std::vector<Fr> T_list_den(1 << (n_pad_vars + d_pad_vars), Fr(1));


    ll* left_children_ll = new ll[1<<(N_pad_vars+n_pad_vars)]();
    ll* right_children_ll = new ll[1<<(N_pad_vars+n_pad_vars)]();
    
    vector<int> new2old(N+1), old2new(N+1);
    for (int i = 1; i <= N; i++){
        fin >> new2old[i];
    }
    for (int i = 1; i <= N; i++){
        fin >> old2new[i];
    }
    
    vector<int> parent(1<<N_pad_vars,0), depth(1<<N_pad_vars,0);
    for (int i = 0; i < N; i++){
        fin >> parent[i];
    }
    for (int i = 0; i < N; i++){
        fin >> depth[i];
    }
    
    vector<int> leftchildren_id(1<<n_pad_vars,0), rightchildren_id(1<<n_pad_vars,0);
    for (int i = 0; i < n; i++){
        fin >> leftchildren_id[i];
    }
    for (int i = 0; i < n; i++){
        fin >> rightchildren_id[i];
    }
    
    // leftchildren, rightchildren should be saved as sparse matrix actually
 
    vector<vector<ll>> left_children_indicator(1<<n_pad_vars, vector<ll>(1<<N_pad_vars,0));
    vector<Fr> left_children_Fr(1u<<(n_pad_vars+N_pad_vars),Fr(0));
    for (int i = 0; i < n; i++){
        for (int j = 0; j < N; j++){
            fin >> left_children_indicator[i][j];
            left_children_ll[i*(1<<N_pad_vars)+j] = left_children_indicator[i][j];
            left_children_Fr[i*(1<<N_pad_vars)+j] = Fr(left_children_ll[i*(1<<N_pad_vars)+j]);
        }
    }
  
    vector<vector<ll>> right_children_indicator(1<<n_pad_vars, vector<ll>(1<<N_pad_vars,0));
    vector<Fr> right_children_Fr(1u<<(n_pad_vars+N_pad_vars),Fr(0));
    for (int i = 0; i < n; i++){
        for (int j = 0; j < N; j++){
            fin >> right_children_indicator[i][j];
            right_children_ll[i*(1<<N_pad_vars)+j] = right_children_indicator[i][j];
            right_children_Fr[i*(1<<N_pad_vars)+j] =Fr(right_children_ll[i*(1<<N_pad_vars)+j]);
        }
    }
    

    vector<vector<Rational_Fr>> L_list(1<<d_pad_vars, vector<Rational_Fr>(1<<N_pad_vars));
    for (int i = 0; i < N; i++){
        for (int j = 0; j < d; j++){
            string s;
            fin >> s;
            L_list[j][i] = parseFraction(s);
            L_list_num_Fr[j*(1u<<N_pad_vars)+i] = L_list[j][i].numerator;
            L_list_den_Fr[j*(1u<<N_pad_vars)+i] = L_list[j][i].denominator;

        }
    }

    vector<vector<Rational_Fr>> R_list(1<<d_pad_vars, vector<Rational_Fr>(1<<N_pad_vars));
    for (int i = 0; i < N; i++){
        for (int j = 0; j < d; j++){
            string s;
            fin >> s;
            R_list[j][i] = parseFraction(s);
            R_list_num_Fr[j*(1u<<N_pad_vars)+i] = R_list[j][i].numerator;
            R_list_den_Fr[j*(1u<<N_pad_vars)+i] = R_list[j][i].denominator;

        }
    }
    

    vector<vector<Rational_Fr>> T_list(1<<n_pad_vars, vector<Rational_Fr>(1<<d_pad_vars));
    for (int i = 0; i < n; i++){
        for (int j = 0; j < d; j++){
            string s;
            fin >> s;
            T_list[i][j] = parseFraction(s);
            T_list_Fr[i*(1u<<d_pad_vars)+j] = T_list[i][j].numerator;

        }
    }
    

    vector<Rational_Fr> eta_list(1<<n_pad_vars);
    for (int i = 0; i < n; i++){
        string s;
        fin >> s;
        eta_list[i] = parseFraction(s);
        eta_list_num_Fr[i] = eta_list[i].numerator;
        eta_list_den_Fr[i] = eta_list[i].denominator;

    }
    
    vector<vector<Rational_Fr>> X_list(1<<d_pad_vars, vector<Rational_Fr>(1<<N_pad_vars));
    for (int i = 0; i < N; i++){
        for (int j = 0; j < d; j++){
            string s;
            fin >> s;
            X_list[j][i] = parseFraction(s);
            X_num_Fr[j*(1u<<N_pad_vars)+i] = X_list[j][i].numerator;
            X_den_Fr[j*(1u<<N_pad_vars)+i] = X_list[j][i].denominator;

        }
    }
    
    vector<vector<Rational_Fr>> Y_list(1<<dd_plus_m_pad_vars, vector<Rational_Fr>(1<<N_pad_vars));
    for (int i = 0; i < N; i++){
        for (int k = 0; k < (m+2*d); k++){
            string s;
            fin >> s;
            Y_list[k][i] = parseFraction(s);
            Y_list_num_Fr[k*(1u<<N_pad_vars)+i] = Y_list[k][i].numerator;
            Y_list_den_Fr[k*(1u<<N_pad_vars)+i] = Y_list[k][i].denominator; 

        }
    }
    

    vector<Rational_Fr> obj_list(1<<N_pad_vars);
    for (int i = 0; i < N; i++){
        string s;
        fin >> s;
        obj_list[i] = parseFraction(s);
        V_list_num_Fr[i] = obj_list[i].numerator;
        V_list_den_Fr[i] = obj_list[i].denominator;

    }
    
    fin.close();
    t.start();
    // G1* commitA_num = prover_commit(A_num, g_big, m_pad_vars+d_pad_vars, 16);
    // G1* commitA_den = prover_commit(A_den, g_big, m_pad_vars+d_pad_vars, 16);
    // G1* commitb_num = prover_commit(b_num, g_big, m_pad_vars, 16);
    // G1* commitb_den = prover_commit(b_den, g_big, m_pad_vars, 16);
    // G1* commitc_num = prover_commit(c_num, g_big, d_pad_vars, 16);
    // G1* commitc_den = prover_commit(c_den, g_big, d_pad_vars, 16);
    // G1* commitL_num = prover_commit(L_list_num, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitL_den = prover_commit(L_list_den, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitR_num = prover_commit(R_list_num, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitR_den = prover_commit(R_list_den, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitX_num = prover_commit(X_num, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitX_den = prover_commit(X_den, g_big, N_pad_vars+d_pad_vars, 16);
    // G1* commitY_num = prover_commit(Y_list_num, g_big, N_pad_vars+dd_plus_m_pad_vars, 16);
    // G1* commitY_den = prover_commit(Y_list_den, g_big, N_pad_vars+dd_plus_m_pad_vars, 16);
    // G1* commiteta_num = prover_commit(eta_list_num, g_big, n_pad_vars, 16);
    // G1* commiteta_den = prover_commit(eta_list_den, g_big, n_pad_vars, 16);
    // G1* commitV_num = prover_commit(V_list_num, g_big, N_pad_vars, 16);
    // G1* commitV_den = prover_commit(V_list_den, g_big, N_pad_vars, 16);
    // G1* commitT = prover_commit(T_list_ll, g_big, n_pad_vars+d_pad_vars, 16);
    G1* commitA_num = prover_commit_Fr(A_num_Fr.data(), g_big, m_pad_vars + d_pad_vars, 16);
    G1* commitA_den = prover_commit_Fr(A_den_Fr.data(), g_big, m_pad_vars + d_pad_vars, 16);
    G1* commitb_num = prover_commit_Fr(b_num_Fr.data(), g_big, m_pad_vars, 16);
    G1* commitb_den = prover_commit_Fr(b_den_Fr.data(), g_big, m_pad_vars, 16);
    G1* commitc_num = prover_commit_Fr(c_num_Fr.data(), g_big, d_pad_vars, 16);
    G1* commitc_den = prover_commit_Fr(c_den_Fr.data(), g_big, d_pad_vars, 16);
    G1* commitL_num = prover_commit_Fr(L_list_num_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitL_den = prover_commit_Fr(L_list_den_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitR_num = prover_commit_Fr(R_list_num_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitR_den = prover_commit_Fr(R_list_den_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitX_num = prover_commit_Fr(X_num_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitX_den = prover_commit_Fr(X_den_Fr.data(), g_big, N_pad_vars + d_pad_vars, 16);
    G1* commitY_num = prover_commit_Fr(Y_list_num_Fr.data(), g_big, N_pad_vars + dd_plus_m_pad_vars, 16);
    G1* commitY_den = prover_commit_Fr(Y_list_den_Fr.data(), g_big, N_pad_vars + dd_plus_m_pad_vars, 16);
    G1* commiteta_num = prover_commit_Fr(eta_list_num_Fr.data(), g_big, n_pad_vars, 16);
    G1* commiteta_den = prover_commit_Fr(eta_list_den_Fr.data(), g_big, n_pad_vars, 16);
    G1* commitV_num = prover_commit_Fr(V_list_num_Fr.data(), g_big, N_pad_vars, 16);
    G1* commitV_den = prover_commit_Fr(V_list_den_Fr.data(), g_big, N_pad_vars, 16);
    G1* commitT = prover_commit_Fr(T_list_Fr.data(), g_big, n_pad_vars + d_pad_vars, 16);
    

    // P computes leftchildren*R, rightchildren*L, L_1_n, R_1_n, 1-T 
    // \mathcal{L}\cdot \mathbf{U} = \mathbf{U}_{[1,n]} \circ (1-\mathbf{T}) + \eta \circ \mathbf{T}
    vector<Fr> Minus_T_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> Minus_T_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    for (unsigned int i=0;i<(1u<<d_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<n_pad_vars);j++){
            Minus_T_num[i*(1u<<n_pad_vars)+j] = Fr(1) - T_list_Fr[i*(1u<<n_pad_vars)+j];
        }
    }
    vector<Fr> L_transpose_num(1u<<(N_pad_vars+d_pad_vars),Fr(0));
    vector<Fr> L_transpose_den(1u<<(N_pad_vars+d_pad_vars),Fr(1));
    vector<Fr> R_transpose_num(1u<<(N_pad_vars+d_pad_vars),Fr(0));
    vector<Fr> R_transpose_den(1u<<(N_pad_vars+d_pad_vars),Fr(1));
    for (unsigned int i=0;i<(1u<<N_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            L_transpose_num[i*(1u<<d_pad_vars)+j] = L_list_num_Fr[j*(1u<<N_pad_vars)+i];
            L_transpose_den[i*(1u<<d_pad_vars)+j] = L_list_den_Fr[j*(1u<<N_pad_vars)+i];
            R_transpose_num[i*(1u<<d_pad_vars)+j] = R_list_num_Fr[j*(1u<<N_pad_vars)+i];
            R_transpose_den[i*(1u<<d_pad_vars)+j] = R_list_den_Fr[j*(1u<<N_pad_vars)+i];
        }
    }

    vector<Fr> L_1_n_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> L_1_n_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    for (unsigned int i=0;i<n;i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            L_1_n_num[i*(1u<<d_pad_vars)+j] = L_transpose_num[i*(1u<<d_pad_vars)+j];
            L_1_n_den[i*(1u<<d_pad_vars)+j] = L_transpose_den[i*(1u<<d_pad_vars)+j];
        }
    }
    vector<Fr> R_1_n_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> R_1_n_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    for (unsigned int i=0;i<n;i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            R_1_n_num[i*(1u<<d_pad_vars)+j] = R_transpose_num[i*(1u<<d_pad_vars)+j];
            R_1_n_den[i*(1u<<d_pad_vars)+j] = R_transpose_den[i*(1u<<d_pad_vars)+j];
        }
    }

    G1* commit_L_1_n_num = prover_commit_Fr(L_1_n_num.data(),g_big,n_pad_vars+d_pad_vars);
    G1* commit_L_1_n_den = prover_commit_Fr(L_1_n_den.data(),g_big,n_pad_vars+d_pad_vars);
    G1* commit_R_1_n_num = prover_commit_Fr(R_1_n_num.data(),g_big,n_pad_vars+d_pad_vars);
    G1* commit_R_1_n_den = prover_commit_Fr(R_1_n_den.data(),g_big,n_pad_vars+d_pad_vars);

    vector<Fr> LL_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> LL_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> LR_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> LR_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> RL_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> RL_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> RR_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> RR_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    for (unsigned int i=0;i<n;i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            LL_num[i*(1u<<d_pad_vars)+j] = L_transpose_num[(leftchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            LL_den[i*(1u<<d_pad_vars)+j] = L_transpose_den[(leftchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            LR_num[i*(1u<<d_pad_vars)+j] = R_transpose_num[(leftchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            LR_den[i*(1u<<d_pad_vars)+j] = R_transpose_den[(leftchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            RL_num[i*(1u<<d_pad_vars)+j] = L_transpose_num[(rightchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            RL_den[i*(1u<<d_pad_vars)+j] = L_transpose_den[(rightchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            RR_num[i*(1u<<d_pad_vars)+j] = R_transpose_num[(rightchildren_id[i]-1)*(1u<<d_pad_vars)+j];
            RR_den[i*(1u<<d_pad_vars)+j] = R_transpose_den[(rightchildren_id[i]-1)*(1u<<d_pad_vars)+j];
        }
    }
    G1* commit_LL_num=prover_commit_Fr(LL_num.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_LL_den=prover_commit_Fr(LL_den.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_LR_num=prover_commit_Fr(LR_num.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_LR_den=prover_commit_Fr(LR_den.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_RR_num=prover_commit_Fr(RR_num.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_RR_den=prover_commit_Fr(RR_den.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_RL_num=prover_commit_Fr(RL_num.data(),g_big,n_pad_vars+d_pad_vars,16);
    G1* commit_RL_den=prover_commit_Fr(RL_den.data(),g_big,n_pad_vars+d_pad_vars,16);

    communication += d_pad_vars+n_pad_vars;
    cout<<"commit!"<<endl;
    //t.stop("commit:",true,false);
    //t.start();
    // prove LL=L1,n; RU=U1,n
    std::cout<<"check bound constraint:"<<endl;
    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok1_1 = Rational_Equal(LL_num,LL_den,L_1_n_num,L_1_n_den,d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok1_1)){
        std::cout<<"LL!=L[1,n]"<<std::endl;
        return 0;
    }
    openCommit(LL_num,std::get<5>(ok1_1).data(),std::get<1>(ok1_1),G_big,g_big,commit_LL_num,d_pad_vars+n_pad_vars);
    openCommit(LL_den,std::get<5>(ok1_1).data(),std::get<2>(ok1_1),G_big,g_big,commit_LL_den,d_pad_vars+n_pad_vars);
    openCommit(L_1_n_num,std::get<5>(ok1_1).data(),std::get<3>(ok1_1),G_big,g_big,commit_L_1_n_num,d_pad_vars+n_pad_vars);
    openCommit(L_1_n_den,std::get<5>(ok1_1).data(),std::get<4>(ok1_1),G_big,g_big,commit_L_1_n_den,d_pad_vars+n_pad_vars);
    std::cout<<"LL == L[1,n]"<<std::endl;

    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok2 = Rational_Equal(RR_num,RR_den,R_1_n_num,R_1_n_den,d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok2)){
        std::cout<<"RU!=U[1,n]"<<std::endl;
        return 0;
    }
    openCommit(RR_num,std::get<5>(ok2).data(),std::get<1>(ok2),G_big,g_big,commit_RR_num,d_pad_vars+n_pad_vars);
    openCommit(RR_den,std::get<5>(ok2).data(),std::get<2>(ok2),G_big,g_big,commit_RR_den,d_pad_vars+n_pad_vars);
    openCommit(R_1_n_num,std::get<5>(ok2).data(),std::get<3>(ok2),G_big,g_big,commit_R_1_n_num,d_pad_vars+n_pad_vars);
    openCommit(R_1_n_den,std::get<5>(ok2).data(),std::get<4>(ok2),G_big,g_big,commit_R_1_n_den,d_pad_vars+n_pad_vars);
    std::cout<<"RU == U[1,n]"<<std::endl;

    vector<Fr> eta_padding_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> eta_padding_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    for (unsigned int i=0;i<(1u<<n_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            eta_padding_num[i*(1u<<d_pad_vars)+j] = eta_list_num_Fr[i];
        }
    }
    // Prove LU and RL
    vector<Fr> LU_part1_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> LU_part2_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> LU_part1_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> LU_part2_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> LU_RHS_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> LU_RHS_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));


    for (unsigned int i=0;i<(1u<<n_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            LU_part1_num[i*(1u<<d_pad_vars)+j] = R_1_n_num[i*(1u<<d_pad_vars)+j] * Minus_T_num[i*(1u<<d_pad_vars)+j];
            LU_part1_den[i*(1u<<d_pad_vars)+j] = R_1_n_den[i*(1u<<d_pad_vars)+j] * Minus_T_den[i*(1u<<d_pad_vars)+j];
            LU_part2_num[i*(1u<<d_pad_vars)+j] = eta_list_num_Fr[i] * T_list_Fr[i*(1u<<d_pad_vars)+j];
            assert(eta_list_den_Fr[i] == Fr(1));
            LU_RHS_num[i*(1u<<d_pad_vars)+j] = LU_part1_num[i*(1u<<d_pad_vars)+j] * LU_part2_den[i*(1u<<d_pad_vars)+j] + LU_part1_den[i*(1u<<d_pad_vars)+j] * LU_part2_num[i*(1u<<d_pad_vars)+j];
            LU_RHS_den[i*(1u<<d_pad_vars)+j] = LU_part2_den[i*(1u<<d_pad_vars)+j] * LU_part1_den[i*(1u<<d_pad_vars)+j];
        }
    }
    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok3_1 = Rational_Equal(LR_num,LR_den,LU_RHS_num,LU_RHS_den,d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok3_1)){
        std::cout<<"LU!=RHS"<<std::endl;
        return 0;
    }
    openCommit(LR_num,std::get<5>(ok3_1).data(),std::get<1>(ok3_1),G_big,g_big,commit_LR_num,d_pad_vars+n_pad_vars);
    openCommit(LR_den,std::get<5>(ok3_1).data(),std::get<2>(ok3_1),G_big,g_big,commit_LR_den,d_pad_vars+n_pad_vars);

    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok3_2 = 
    Rational_Addition(LU_part1_num,LU_part1_den,LU_part2_num,LU_part2_den,std::get<3>(ok3_1),std::get<4>(ok3_1),std::get<5>(ok3_1),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok3_2)){
        std::cout<<"LU!=RHS"<<std::endl;
        return 0;
    }
    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok3_3 = 
    Rational_Hadamard_A_B(R_1_n_num,R_1_n_den,Minus_T_num,Minus_T_den,std::get<1>(ok3_2),std::get<2>(ok3_2),std::get<5>(ok3_2),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok3_3)){
        std::cout<<"LU!=RHS"<<std::endl;
        return 0;
    }
    openCommit(R_1_n_num,std::get<5>(ok3_3).data(),std::get<1>(ok3_3),G_big,g_big,commit_R_1_n_num,n_pad_vars+d_pad_vars);
    openCommit(R_1_n_den,std::get<5>(ok3_3).data(),std::get<2>(ok3_3),G_big,g_big,commit_R_1_n_den,n_pad_vars+d_pad_vars);

    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok3_4 = 
    Rational_Hadamard_A_B(eta_padding_num,eta_padding_den,T_list_Fr,T_list_den,std::get<3>(ok3_2),std::get<4>(ok3_2),std::get<5>(ok3_2),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok3_4)){
        std::cout<<"LU!=RHS"<<std::endl;
        return 0;
    }

    openCommit(T_list_Fr,std::get<5>(ok3_4).data(),std::get<3>(ok3_4),G_big,g_big,commitT,n_pad_vars+d_pad_vars);
    assert(std::get<4>(ok3_4) == Fr(1));

    std::cout<<"LU correct"<<std::endl;

    // t.stop("LL LU RL RU commit total time:",true,false);
    // -------------------------------------------------------------------------------------------------------------------------------
    // t.start();
    vector<Fr> eta_padding_num_plus_1(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    for (unsigned int i=0;i<(1u<<n_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            eta_padding_num_plus_1[i*(1u<<d_pad_vars)+j] = eta_list_num_Fr[i]+Fr(1);
        }
    }
    vector<Fr> RL_part1_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> RL_part2_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> RL_part1_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> RL_part2_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));
    vector<Fr> RL_RHS_num(1u<<(d_pad_vars+n_pad_vars),Fr(0));
    vector<Fr> RL_RHS_den(1u<<(d_pad_vars+n_pad_vars),Fr(1));


    for (unsigned int i=0;i<(1u<<n_pad_vars);i++){
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            RL_part1_num[i*(1u<<d_pad_vars)+j] = L_1_n_num[i*(1u<<d_pad_vars)+j] * Minus_T_num[i*(1u<<d_pad_vars)+j];
            RL_part1_den[i*(1u<<d_pad_vars)+j] = L_1_n_den[i*(1u<<d_pad_vars)+j] * Minus_T_den[i*(1u<<d_pad_vars)+j];
            RL_part2_num[i*(1u<<d_pad_vars)+j] = (eta_list_num_Fr[i] + Fr(1)) * T_list_Fr[i*(1u<<d_pad_vars)+j];
            assert(eta_list_den_Fr[i] == Fr(1));
            RL_RHS_num[i*(1u<<d_pad_vars)+j] = RL_part1_num[i*(1u<<d_pad_vars)+j] * RL_part2_den[i*(1u<<d_pad_vars)+j] + RL_part1_den[i*(1u<<d_pad_vars)+j] * RL_part2_num[i*(1u<<d_pad_vars)+j];
            RL_RHS_den[i*(1u<<d_pad_vars)+j] = RL_part2_den[i*(1u<<d_pad_vars)+j] * RL_part1_den[i*(1u<<d_pad_vars)+j];
        }
    }
    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok4_1 = Rational_Equal(RL_num,RL_den,RL_RHS_num,RL_RHS_den,d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok4_1))
    {
        std::cout<<"RL!=RHS"<<std::endl;
        return 0;
    }
    openCommit(RL_num,std::get<5>(ok4_1).data(),std::get<1>(ok4_1),G_big,g_big,commit_RL_num,d_pad_vars+n_pad_vars);
    openCommit(RL_den,std::get<5>(ok4_1).data(),std::get<2>(ok4_1),G_big,g_big,commit_RL_den,d_pad_vars+n_pad_vars);

    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok4_2 = 
    Rational_Addition(RL_part1_num,RL_part1_den,RL_part2_num,RL_part2_den,std::get<3>(ok4_1),std::get<4>(ok4_1),std::get<5>(ok4_1),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok4_2)){
        std::cout<<"RL!=RHS"<<std::endl;
        return 0;
    }
    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok4_3 = 
    Rational_Hadamard_A_B(L_1_n_num,L_1_n_den,Minus_T_num,Minus_T_den,std::get<1>(ok4_2),std::get<2>(ok4_2),std::get<5>(ok4_2),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok4_3)){
        std::cout<<"RL!=RHS"<<std::endl;
        return 0;
    }
    openCommit(L_1_n_num,std::get<5>(ok4_3).data(),std::get<1>(ok4_3),G_big,g_big,commit_L_1_n_num,n_pad_vars+d_pad_vars);
    openCommit(L_1_n_den,std::get<5>(ok4_3).data(),std::get<2>(ok4_3),G_big,g_big,commit_L_1_n_den,n_pad_vars+d_pad_vars);

    std::tuple<bool, Fr, Fr,Fr,Fr, std::vector<Fr>> ok4_4 = 
    Rational_Hadamard_A_B(eta_padding_num_plus_1,eta_padding_den,T_list_Fr,T_list_den,std::get<3>(ok4_2),std::get<4>(ok4_2),std::get<5>(ok4_2),d_pad_vars+n_pad_vars,G_big,g_big);
    if(!std::get<0>(ok4_4)){
        std::cout<<"RL!=RHS"<<std::endl;
        return 0;
    }

    openCommit(T_list_Fr,std::get<5>(ok4_4).data(),std::get<3>(ok4_4),G_big,g_big,commitT,n_pad_vars+d_pad_vars);
    assert(std::get<4>(ok4_4) == Fr(1));

    std::cout<<"RL correct"<<std::endl;
// -------------------------------------------------------------------------------------------------------------------------------------------------------------
    int Nega_size = 16;
    vector<Fr> Greater_zero_table = buildPosRange(Nega_size);
    std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok5 = 
    Rational_Range_Proof_Lasso(L_transpose_num,L_transpose_den,R_transpose_num,R_transpose_den, Greater_zero_table,d_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok5))
    {
        return 0;
    }
    cout<<"L<=U protocol passed"<<endl;
    vector<Fr> r_transposed_N_d(N_pad_vars+d_pad_vars,Fr(0));
    for (unsigned int i=0;i<N_pad_vars;i++){
        r_transposed_N_d[i] = std::get<5>(ok5)[d_pad_vars+i];
    }
    for (unsigned int i=0;i<d_pad_vars;i++){
        r_transposed_N_d[N_pad_vars+i] = std::get<5>(ok5)[i];
    }
    openCommit(L_list_num_Fr,r_transposed_N_d.data(),std::get<1>(ok5),G_big,g_big,commitL_num,N_pad_vars+d_pad_vars);
    openCommit(L_list_den_Fr,r_transposed_N_d.data(),std::get<2>(ok5),G_big,g_big,commitL_den,N_pad_vars+d_pad_vars);
    openCommit(R_list_num_Fr,r_transposed_N_d.data(),std::get<3>(ok5),G_big,g_big,commitR_num,N_pad_vars+d_pad_vars);
    openCommit(R_list_den_Fr,r_transposed_N_d.data(),std::get<4>(ok5),G_big,g_big,commitR_den,N_pad_vars+d_pad_vars);
    std::cout<<"LU correct"<<std::endl;
    // ----------------------------------------------------------------------------------------------------------------------------------------------
    // prove AX<=b
    vector<Fr> AX_num(1u<<(m_pad_vars+N_pad_vars),Fr(0));
    vector<Fr> AX_den(1u<<(m_pad_vars+N_pad_vars),Fr(1));
    // for (unsigned int i=0;i<(1u<<m_pad_vars);i++){
    //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    for (unsigned int i=0;i<m;i++){
        for (unsigned int j=0;j<N;j++){
            Fr current_num = Fr(0);
            Fr current_den = Fr(1);
            for (unsigned int k=0;k<d;k++){
            // for (unsigned int k=0;k<(1u<<(d_pad_vars));k++){
                // cout<<"AX["<<i<<","<<j<<"] = "<<current_num<<" / "<<current_den<<" + "<<A_num_Fr[i*(1u<<d_pad_vars)+k]<<" / "<<A_den_Fr[i*(1u<<d_pad_vars)+k]<<"*"<<X_num_Fr[k*(1u<<N_pad_vars)+j]<<"/"<<X_den_Fr[k*(1u<<N_pad_vars)+j]<<"=";
                if (A_num_Fr[i*(1u<<d_pad_vars)+k] * X_num_Fr[k*(1u<<N_pad_vars)+j] == Fr(0)){
                    continue;
                }
                current_num = current_num * A_den_Fr[i*(1u<<d_pad_vars)+k] * X_den_Fr[k*(1u<<N_pad_vars)+j] + current_den * A_num_Fr[i*(1u<<d_pad_vars)+k] * X_num_Fr[k*(1u<<N_pad_vars)+j];
                if (current_num == Fr(0)){
                    current_den = Fr(1);
                }
                else
                {
                    current_den = current_den * A_den_Fr[i*(1u<<d_pad_vars)+k] * X_den_Fr[k*(1u<<N_pad_vars)+j];
                }
                // cout<<current_num<<"/"<<current_den<<endl;
            }
            AX_num[i*(1u<<N_pad_vars)+j] = current_num;
            AX_den[i*(1u<<N_pad_vars)+j] = current_den;
        }
    }
    // t.stop("compute AX",true,false);
    // t.start();
    G1* commit_AX_num = prover_commit_Fr(AX_num.data(),g_big,m_pad_vars+N_pad_vars,16);
    G1* commit_AX_den = prover_commit_Fr(AX_den.data(),g_big,m_pad_vars+N_pad_vars,16);
    vector<Fr> b_extend_num(1u<<(m_pad_vars+N_pad_vars),Fr(0));
    vector<Fr> b_extend_den(1u<<(m_pad_vars+N_pad_vars),Fr(1));
    for (unsigned int i=0;i<(1u<<m_pad_vars);i++){
        for (unsigned int j=0;j<N;j++){
            b_extend_num[i*(1u<<N_pad_vars)+j]= b_num_Fr[i];
            b_extend_den[i*(1u<<N_pad_vars)+j]= b_den_Fr[i];
        }
    }
    // for (unsigned int i=0;i<(1u<<m_pad_vars);i++){
    //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    //         cout<<AX_num[i*(1u<<N_pad_vars)+j]<<"/"<<AX_den[i*(1u<<N_pad_vars)+j]<<"   ";
    //     }
    //     cout<<endl;
    // }
    // for (unsigned int i=0;i<(1u<<m_pad_vars);i++){
    //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    //         cout<<b_extend_num[i*(1u<<N_pad_vars)+j]<<"/"<<b_extend_den[i*(1u<<N_pad_vars)+j]<<"   ";
    //     }
    //     cout<<endl;
    // }
    // std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok6_1 = 
    // Rational_Range_Proof(AX_num,AX_den,b_extend_num,b_extend_den,Minus_zero_table,m_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok6_1 = 
    Rational_Range_Proof_Lasso(AX_num,AX_den,b_extend_num,b_extend_den,Greater_zero_table ,m_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok6_1)){
        std::cout<<"AX should not > b!"<<std::endl;
        return 0;
    }
    cout<<"AX<=b protocol correct"<<endl;
    openCommit(AX_num,std::get<5>(ok6_1).data(),std::get<1>(ok6_1),G_big,g_big,commit_AX_num,m_pad_vars+N_pad_vars);
    openCommit(AX_den,std::get<5>(ok6_1).data(),std::get<2>(ok6_1),G_big,g_big,commit_AX_den,m_pad_vars+N_pad_vars);
    cout<<"AX<=b"<<endl;
    std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> ok6_2
    = Rational_MatrixMul(A_num_Fr,A_den_Fr,X_num_Fr,X_den_Fr,AX_num,AX_den,m_pad_vars,d_pad_vars,N_pad_vars,G_big,g_big);
    cout<<"AX MatMul protocol passed"<<endl;
    openCommit(A_num_Fr,std::get<2>(ok6_2).data(),std::get<1>(ok6_2),G_big,g_big,commitA_num,m_pad_vars+d_pad_vars);
    openCommit(A_den_Fr,std::get<4>(ok6_2).data(),std::get<3>(ok6_2),G_big,g_big,commitA_den,m_pad_vars+d_pad_vars);
    openCommit(X_num_Fr,std::get<6>(ok6_2).data(),std::get<5>(ok6_2),G_big,g_big,commitX_num,N_pad_vars+d_pad_vars);
    openCommit(X_den_Fr,std::get<8>(ok6_2).data(),std::get<7>(ok6_2),G_big,g_big,commitX_den,N_pad_vars+d_pad_vars);
    openCommit(AX_num,std::get<10>(ok6_2).data(),std::get<9>(ok6_2),G_big,g_big,commit_AX_num,m_pad_vars+N_pad_vars);
    openCommit(AX_den,std::get<12>(ok6_2).data(),std::get<11>(ok6_2),G_big,g_big,commit_AX_den,m_pad_vars+N_pad_vars);
    cout<<"AX correct"<<endl;
// ------------------------------------------------------------------------------------------------------------------------------------ 
    // std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok8 = 
    // Rational_Range_Proof(X_num_Fr,X_den_Fr,R_list_num_Fr,R_list_den_Fr,Minus_zero_table,d_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok8 = 
    Rational_Range_Proof_Lasso(X_num_Fr,X_den_Fr,R_list_num_Fr,R_list_den_Fr,Greater_zero_table ,d_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    if(!std::get<0>(ok8))
    {    
        return 0;
    }
    
    openCommit(R_list_num_Fr,std::get<5>(ok8).data(),std::get<3>(ok8),G_big,g_big,commitR_num,d_pad_vars+N_pad_vars);
    openCommit(R_list_den_Fr,std::get<5>(ok8).data(),std::get<4>(ok8),G_big,g_big,commitR_den,d_pad_vars+N_pad_vars);
    openCommit(X_num_Fr,std::get<5>(ok8).data(),std::get<1>(ok8),G_big,g_big,commitX_num,d_pad_vars+N_pad_vars);
    openCommit(X_den_Fr,std::get<5>(ok8).data(),std::get<2>(ok8),G_big,g_big,commitX_den,d_pad_vars+N_pad_vars);
    
// --------------------------------------------------------------------------------------------------------------------------------------------------------------
    // prove A_augY>=C Y>=0
    ll ddd = 1LL<<d_pad_vars;
    ll NNN = 1LL<<N_pad_vars;
    // vector<Fr> A_aug_num(1u<<(d_pad_vars + dd_plus_m_pad_vars),Fr(0));
    // vector<Fr> A_aug_den(1u<<(d_pad_vars + dd_plus_m_pad_vars),Fr(1));
    // for (unsigned int i=0;i<d;i++){
    //     for (unsigned int j=0;j<m;j++){
    //         A_aug_num[i*(1u<<dd_plus_m_pad_vars)+j] = A_num_Fr[j*(1u<<d_pad_vars)+i];
    //         A_aug_den[i*(1u<<dd_plus_m_pad_vars)+j] = A_den_Fr[j*(1u<<d_pad_vars)+i];
    //     }
    // }
    // for (unsigned int i=0;i<d;i++){
    //     A_aug_num[i*(1u<<dd_plus_m_pad_vars)+m+i] = Fr(-1);
    //     A_aug_num[i*(1u<<dd_plus_m_pad_vars)+m+d+i] = Fr(1);
    // }
    // vector<Fr> AY_num(1u<<(d_pad_vars+N_pad_vars),Fr(0));
    // vector<Fr> AY_den(1u<<(d_pad_vars+N_pad_vars),Fr(1));
    // for (unsigned int i=0;i<(1u<<d_pad_vars);i++){
    //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    //         Fr current_num = Fr(0);
    //         Fr current_den = Fr(1);
    //         for (unsigned int k=0;k<(1u<<(dd_plus_m_pad_vars));k++){
    //             current_num = current_num * A_aug_den[i*(1u<<dd_plus_m_pad_vars)+k] * Y_list_den_Fr[k*(1u<<N_pad_vars)+j] + current_den * A_aug_num[i*(1u<<dd_plus_m_pad_vars)+k] *  Y_list_num_Fr[k*(1u<<N_pad_vars)+j];
    //             current_den = current_den * A_aug_den[i*(1u<<dd_plus_m_pad_vars)+k] * Y_list_den_Fr[k*(1u<<N_pad_vars)+j];
    //         }
    //         AY_num[i*(1u<<N_pad_vars)+j] = current_num;
    //         AY_den[i*(1u<<N_pad_vars)+j] = current_den;
    //     }
    // }
    vector<Fr> A_aug_num(1u<<(d_pad_vars + dd_plus_m_pad_vars),Fr(0));
    vector<Fr> A_aug_den(1u<<(d_pad_vars + dd_plus_m_pad_vars),Fr(1));
    for (unsigned int i=0;i<d;i++){
        for (unsigned int j=0;j<m;j++){
            A_aug_num[i*(1u<<dd_plus_m_pad_vars)+j] = A_num_Fr[j*(1u<<d_pad_vars)+i];
            A_aug_den[i*(1u<<dd_plus_m_pad_vars)+j] = A_den_Fr[j*(1u<<d_pad_vars)+i];
        }
    }
    for (unsigned int i=0;i<d;i++){
        A_aug_num[i*(1u<<dd_plus_m_pad_vars)+m+i] = Fr(-1);
        A_aug_num[i*(1u<<dd_plus_m_pad_vars)+m+d+i] = Fr(1);
    }
    vector<Fr> AY_num(1u<<(d_pad_vars+N_pad_vars),Fr(0));
    vector<Fr> AY_den(1u<<(d_pad_vars+N_pad_vars),Fr(1));
    for (unsigned int i=0;i<d;i++){
        for (unsigned int j=0;j<N;j++){
            Fr current_num = Fr(0);
            Fr current_den = Fr(1);
            for (unsigned int k=0;k<m;k++){
                if (A_num_Fr[k*ddd+i] *  Y_list_num_Fr[k*NNN+j] == Fr(0)){
                    continue;
                }
                current_num = current_num * A_den_Fr[k*ddd+i] * Y_list_den_Fr[k*NNN+j] + current_den * A_num_Fr[k*ddd+i] *  Y_list_num_Fr[k*NNN+j];
                current_den = current_den * A_den_Fr[k*ddd+i] * Y_list_den_Fr[k*NNN+j];
            }
            current_num = current_num * Y_list_den_Fr[(i+m)*NNN+j] + current_den * Fr(-1) *  Y_list_num_Fr[(i+m)*NNN+j];
            current_den = current_den * Y_list_den_Fr[(i+m)*NNN+j];
            current_num = current_num * Y_list_den_Fr[(i+m+d)*NNN+j] + current_den *  Y_list_num_Fr[(i+m+d)*NNN+j];
            current_den = current_den * Y_list_den_Fr[(i+m+d)*NNN+j];
            AY_num[i*NNN+j] = current_num;
            AY_den[i*NNN+j] = current_den;
        }
    }
    G1* commit_AY_num = prover_commit_Fr(AY_num.data(),g_big,d_pad_vars+N_pad_vars,16);
    G1* commit_AY_den = prover_commit_Fr(AY_den.data(),g_big,d_pad_vars+N_pad_vars,16);

    vector<Fr> c_extend_num(1u<<(d_pad_vars+N_pad_vars),Fr(0));
    vector<Fr> c_extend_den(1u<<(d_pad_vars+N_pad_vars),Fr(1));
    for (unsigned int i=0;i<(1u<<d_pad_vars);i++){
        for (unsigned int j=0;j<N;j++){
            c_extend_num[i*(1u<<N_pad_vars)+j]= c_num_Fr[i];
            c_extend_den[i*(1u<<N_pad_vars)+j]= c_den_Fr[i];
        }
    }
    // // for (unsigned int i=0;i<(1u<<d_pad_vars);i++){
    // //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    // //         cout<<AY_num[i*(1u<<N_pad_vars)+j]<<"/"<<AY_den[i*(1u<<N_pad_vars)+j]<<"   ";
    // //     }
    // //     cout<<endl;
    // // }
    // // for (unsigned int i=0;i<(1u<<d_pad_vars);i++){
    // //     for (unsigned int j=0;j<(1u<<N_pad_vars);j++){
    // //         cout<<c_extend_num[i*(1u<<N_pad_vars)+j]<<"/"<<c_extend_den[i*(1u<<N_pad_vars)+j]<<"   ";
    // //     }
    // //     cout<<endl;
    // // }

    // // std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok9_1 = 
    // // Rational_Range_Proof(AY_num,AY_den,c_extend_num,c_extend_den,Greater_zero_table,d_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    // std::tuple<bool, Fr, Fr,Fr,Fr,std::vector<Fr>, Fr,std::vector<Fr>> ok9_1 = 
    // Rational_Range_Proof_Lasso(c_extend_num,c_extend_den,AY_num,AY_den,Greater_zero_table,d_pad_vars+N_pad_vars,Nega_size,G_big,g_big);
    // if(!std::get<0>(ok9_1)){
    //     std::cout<<"AY should not < c!"<<std::endl;
    //     return 0;
    // }
    // cout<<"AY>=c protocol correct"<<endl;
    // openCommit(AY_num,std::get<5>(ok9_1).data(),std::get<3>(ok9_1),G_big,g_big,commit_AY_num,d_pad_vars+N_pad_vars);
    // openCommit(AY_den,std::get<5>(ok9_1).data(),std::get<4>(ok9_1),G_big,g_big,commit_AY_den,d_pad_vars+N_pad_vars);
    cout<<"AY>=c"<<endl;

    std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> ok9_2
    = Rational_MatrixMul(A_aug_num,A_aug_den,Y_list_num_Fr,Y_list_den_Fr,AY_num,AY_den,d_pad_vars,dd_plus_m_pad_vars,N_pad_vars,G_big,g_big);
    cout<<"AY Mul protocol passed"<<endl;
    // A_aug can be open with virtual oracle， not the bottleneck.
    openCommit(Y_list_num_Fr,std::get<6>(ok9_2).data(),std::get<5>(ok9_2),G_big,g_big,commitY_num,dd_plus_m_pad_vars+N_pad_vars);
    openCommit(Y_list_den_Fr,std::get<8>(ok9_2).data(),std::get<7>(ok9_2),G_big,g_big,commitY_den,dd_plus_m_pad_vars+N_pad_vars);
    openCommit(AY_num,std::get<10>(ok9_2).data(),std::get<9>(ok9_2),G_big,g_big,commit_AY_num,d_pad_vars+N_pad_vars);
    openCommit(AY_den,std::get<12>(ok9_2).data(),std::get<11>(ok9_2),G_big,g_big,commit_AY_den,d_pad_vars+N_pad_vars);
    
    // ---------------------------------------------------------------------------------------------------------------------------------------------
    // prove c^TX = V         1*d * d*N = 1*N
    std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> ok10
    = Rational_MatrixMul(c_num_Fr,c_den_Fr,X_num_Fr,X_den_Fr,V_list_num_Fr,V_list_den_Fr,0,d_pad_vars,N_pad_vars,G_big,g_big);
    cout<<"cTX rationalMul protocol passed"<<endl;
    openCommit(c_num_Fr,std::get<2>(ok10).data(),std::get<1>(ok10),G_big,g_big,commitc_num,0+d_pad_vars);
    openCommit(c_den_Fr,std::get<4>(ok10).data(),std::get<3>(ok10),G_big,g_big,commitc_den,0+d_pad_vars);
    openCommit(X_num_Fr,std::get<6>(ok10).data(),std::get<5>(ok10),G_big,g_big,commitX_num,d_pad_vars+N_pad_vars);
    openCommit(X_den_Fr,std::get<8>(ok10).data(),std::get<7>(ok10),G_big,g_big,commitX_den,d_pad_vars+N_pad_vars);
    openCommit(V_list_num_Fr,std::get<10>(ok10).data(),std::get<9>(ok10),G_big,g_big,commitV_num,0+N_pad_vars);
    openCommit(V_list_den_Fr,std::get<12>(ok10).data(),std::get<11>(ok10),G_big,g_big,commitV_den,0+N_pad_vars);
    cout<<"cT * X correct"<<endl;
    // ---------------------------------------------------------------------------------------------------------------------------------------------
    // prove AY Dot Hadamard
    vector<Fr> Lc_num(1u<<N_pad_vars,Fr(0));
    vector<Fr> Lc_den(1u<<N_pad_vars,Fr(1));
    for (unsigned int i=0;i<(1u<<N_pad_vars);i++){
        Fr current_num = Fr(0);
        Fr current_den = Fr(1);
        for (unsigned int j=0;j<(1u<<d_pad_vars);j++){
            current_num = current_num * c_den_Fr[j] * L_list_den_Fr[j*(1u<<N_pad_vars)+i] + current_den * c_num_Fr[j] *  L_list_num_Fr[j*(1u<<N_pad_vars)+i];
            current_den = current_den * c_den_Fr[j] * L_list_den_Fr[j*(1u<<N_pad_vars)+i];
        }
        Lc_num[i] = current_num;
        Lc_den[i] = current_den;
    }
    G1* commit_Lc_num = prover_commit_Fr(Lc_num.data(),g_big,N_pad_vars,16);
    G1* commit_Lc_den = prover_commit_Fr(Lc_den.data(),g_big,N_pad_vars,16);
    std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> ok11_1
    = Rational_MatrixMul(c_num_Fr,c_den_Fr,L_list_num_Fr,L_list_den_Fr,Lc_num,Lc_den,0,d_pad_vars,N_pad_vars,G_big,g_big);
    cout<<"cTL Mul protocol passed"<<endl;
    openCommit(c_num_Fr,std::get<2>(ok11_1).data(),std::get<1>(ok11_1),G_big,g_big,commitc_num,0+d_pad_vars);
    openCommit(c_den_Fr,std::get<4>(ok11_1).data(),std::get<3>(ok11_1),G_big,g_big,commitc_den,0+d_pad_vars);
    openCommit(L_list_num_Fr,std::get<6>(ok11_1).data(),std::get<5>(ok11_1),G_big,g_big,commitL_num,d_pad_vars+N_pad_vars);
    openCommit(L_list_den_Fr,std::get<8>(ok11_1).data(),std::get<7>(ok11_1),G_big,g_big,commitL_den,d_pad_vars+N_pad_vars);
    openCommit(Lc_num,std::get<10>(ok11_1).data(),std::get<9>(ok11_1),G_big,g_big,commit_Lc_num,0+N_pad_vars);
    openCommit(Lc_den,std::get<12>(ok11_1).data(),std::get<11>(ok11_1),G_big,g_big,commit_Lc_den,0+N_pad_vars);
    cout<<"cT * L correct"<<endl;

    vector<Fr> B_aug_num(1u<<(dd_plus_m_pad_vars+N_pad_vars),Fr(0));
    vector<Fr> B_aug_den(1u<<(dd_plus_m_pad_vars+N_pad_vars),Fr(1));
    for (unsigned int i=0;i<m;i++){
        for (unsigned int j=0;j<N;j++){
            B_aug_num[i*(1u<<N_pad_vars)+j] = b_extend_num[i*(1u<<N_pad_vars)+j];
            B_aug_den[i*(1u<<N_pad_vars)+j] = b_extend_den[i*(1u<<N_pad_vars)+j];
        }
    }
    for (unsigned int i=0;i<d;i++){
        for (unsigned int j=0;j<N;j++){
            B_aug_num[(m+i)*(1u<<N_pad_vars)+j] = Fr(0) - L_list_num_Fr[i*(1u<<N_pad_vars)+j];
            B_aug_den[(m+i)*(1u<<N_pad_vars)+j] = L_list_den_Fr[i*(1u<<N_pad_vars)+j];
            B_aug_num[(m+d+i)*(1u<<N_pad_vars)+j] = R_list_num_Fr[i*(1u<<N_pad_vars)+j];
            B_aug_den[(m+d+i)*(1u<<N_pad_vars)+j] = R_list_den_Fr[i*(1u<<N_pad_vars)+j];
        }
    }
    vector<Fr> B_aug_T_num = transpose_power2_matrix<Fr>(B_aug_num, dd_plus_m_pad_vars, N_pad_vars);
    vector<Fr> B_aug_T_den = transpose_power2_matrix<Fr>(B_aug_den, dd_plus_m_pad_vars, N_pad_vars);
    vector<Fr> Y_T_num = transpose_power2_matrix<Fr>(Y_list_num_Fr, dd_plus_m_pad_vars, N_pad_vars);
    vector<Fr> Y_T_den = transpose_power2_matrix<Fr>(Y_list_den_Fr, dd_plus_m_pad_vars, N_pad_vars);

    // for (int i=0;i<(1u<<N_pad_vars);i++){
    //     for (int j=0;j<(1u<<dd_plus_m_pad_vars);j++){
    //         cout<<B_aug_T_num[i*(1u<<dd_plus_m_pad_vars)+j]<<" / "<<B_aug_T_den[i*(1u<<dd_plus_m_pad_vars)+j]<<" ";
    //     }
    //     cout<<endl;
    // }
    // for (int i=0;i<(1u<<N_pad_vars);i++){
    //     for (int j=0;j<(1u<<dd_plus_m_pad_vars);j++){
    //         cout<<Y_T_num[i*(1u<<dd_plus_m_pad_vars)+j]<<" / "<<Y_T_num[i*(1u<<dd_plus_m_pad_vars)+j]<<" ";
    //     }
    //     cout<<endl;
    // }
    // for (int i=0;i<(1u<<N_pad_vars);i++){
    //     cout<<V_list_num_Fr[i]<<" / "<< V_list_den_Fr[i]<<" ";
    // }
    // cout<<endl;

    std::tuple<bool, Fr, std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr,std::vector<Fr>,Fr, std::vector<Fr>> ok11_2 = 
    Rational_Dot_Hadamard(B_aug_T_num,B_aug_T_den,Y_T_num,Y_T_den,V_list_num_Fr,V_list_den_Fr,N_pad_vars,dd_plus_m_pad_vars,G_big,g_big);
    if(!std::get<0>(ok11_2))
    {
        std::cout<<"Dot Hadamard protocol failed"<<std::endl;
        return 0;
    }
    std::cout<<"Dot Hadamard protocol passed"<<std::endl;
    openCommit(V_list_num_Fr,std::get<10>(ok11_2).data(),std::get<9>(ok11_2),G_big,g_big,commitV_num,N_pad_vars);
    openCommit(V_list_den_Fr,std::get<12>(ok11_2).data(),std::get<11>(ok11_2),G_big,g_big,commitV_den,N_pad_vars);
    openCommit(Y_list_num_Fr,transpose_concat<Fr>(std::get<6>(ok11_2), dd_plus_m_pad_vars, N_pad_vars).data(),std::get<5>(ok11_2),G_big,g_big,commitY_num,dd_plus_m_pad_vars+N_pad_vars);
    openCommit(Y_list_den_Fr,transpose_concat<Fr>(std::get<8>(ok11_2), dd_plus_m_pad_vars, N_pad_vars).data(),std::get<7>(ok11_2),G_big,g_big,commitY_den,dd_plus_m_pad_vars+N_pad_vars);
    std::cout<<"Dot Hadamard correct"<<std::endl;
    // return 0;
    t.stop("total time:",true,false);
}
