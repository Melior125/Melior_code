#ifndef IORACLE_RATIONAL_H
#define IORACLE_RATIONAL_H

#include <vector>
#include "Rational_Fr.hpp"

/** 
 * 抽象Oracle接口，给定 n维点 x=(x1,...,xn) ∈ F^n，返回 Rational_Fr 值。
 */
class IOracleRational {
public:
    virtual ~IOracleRational() {}
    virtual Rational_Fr evaluate(const std::vector<Fr>& x) const = 0;
};

#endif // IORACLE_RATIONAL_H

// ------------------------------------------------
// 一个多线性扩展的分式Oracle示例：
// 内部存储 f在 {0,1}^n 上所有点(分式形式)，
// 并可对任意 (r1,...,rn) 做插值评估 O(n*2^n)。
// ------------------------------------------------
class MultilinearExtensionOracle_Rational : public IOracleRational {
private:
    std::vector<Rational_Fr> poly_eval_; // 大小=2^n
    unsigned int n_;

public:
    MultilinearExtensionOracle_Rational(const std::vector<Rational_Fr>& poly_eval,
                                        unsigned int n)
        : poly_eval_(poly_eval), n_(n)
    {
        if(poly_eval_.size() != (1u<<n_)){
            throw std::runtime_error("poly_eval size != 2^n");
        }
    }

    // evaluate(r1,...,rn): 返回 f(r1,...,rn)
    Rational_Fr evaluate(const std::vector<Fr>& x) const override {
        if(x.size()!=n_){
            throw std::runtime_error("Dimension mismatch in evaluate");
        }
        // 创建工作表 T
        std::vector<Rational_Fr> T = poly_eval_;
        size_t sizeT = T.size();

        // 依次处理 n 个变量
        for(unsigned int i=0; i<n_; i++){
            Rational_Fr rVal(x[i], Fr(1)); // 把 x[i]当作 (x[i]/1)
            size_t halfSize = sizeT/2;
            for(size_t j=0; j<halfSize; j++){
                auto t0 = T[2*j];
                auto t1 = T[2*j+1];
                // diff = t1 - t0
                auto diff = Rational_Fr::sub(t1, t0);
                // T'[j] = t0 + diff * rVal
                T[j] = Rational_Fr::add(t0, Rational_Fr::mul(diff, rVal));
            }
            sizeT = halfSize;
        }
        return T[0]; // 最后一个
    }
};
