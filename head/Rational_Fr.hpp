#ifndef RATIONAL_FR_H
#define RATIONAL_FR_H

#include <iostream>
#include <mcl/bn256.hpp>

// 引入 BN256 命名空间
using namespace mcl::bn256;

/**
 * 在有限域 Fr 上实现简单的“分子/分母”有理数表示
 * 形如 (numerator, denominator) 对应 \(\mathrm{num}/\mathrm{den}\)。
 *
 * 注意：
 *  - 未做“分母=0”的特殊情况处理
 *  - 未做约化或检查 gcd, 仅假设 \(\mathrm{den}\neq0\)
 */
class Rational_Fr {
public:
    Fr numerator;   // 分子
    Fr denominator; // 分母

    // 默认构造：0/1
    Rational_Fr() : numerator(0), denominator(1) {}

    // 显式构造
    Rational_Fr(const Fr& num, const Fr& den)
        : numerator(num), denominator(den)
    {}

    // 在调试中打印
    void print() const {
        std::cout << numerator.getStr(16) << "/" << denominator.getStr(16);
    }

    // 加法: (a0/b0) + (a1/b1) = (a0*b1 + a1*b0) / (b0*b1)
    static Rational_Fr add(const Rational_Fr& a, const Rational_Fr& b) {
        Rational_Fr result;
        result.numerator   = a.numerator * b.denominator + b.numerator * a.denominator;
        result.denominator = a.denominator * b.denominator;
        return result;
    }

    // 减法: (a0/b0) - (a1/b1) = (a0*b1 - a1*b0) / (b0*b1)
    static Rational_Fr sub(const Rational_Fr& a, const Rational_Fr& b) {
        Rational_Fr result;
        result.numerator   = a.numerator * b.denominator - b.numerator * a.denominator;
        result.denominator = a.denominator * b.denominator;
        return result;
    }

    // 乘法: (a0/b0) * (a1/b1) = (a0*a1) / (b0*b1)
    static Rational_Fr mul(const Rational_Fr& a, const Rational_Fr& b) {
        Rational_Fr result;
        result.numerator   = a.numerator   * b.numerator;
        result.denominator = a.denominator * b.denominator;
        return result;
    }

    // 除法: (a0/b0) / (a1/b1) = (a0*b1) / (b0*a1)
    static Rational_Fr div(const Rational_Fr& a, const Rational_Fr& b) {
        Rational_Fr result;
        result.numerator   = a.numerator   * b.denominator;
        result.denominator = a.denominator * b.numerator;
        return result;
    }

    // 相等性判断: (a0/b0) == (a1/b1)  <=>  a0*b1 == a1*b0
    static bool eq(const Rational_Fr& a, const Rational_Fr& b) {
        Fr lhs = a.numerator * b.denominator;
        Fr rhs = a.denominator * b.numerator;
        return lhs == rhs;
    }

    // 加法
    Rational_Fr operator+(const Rational_Fr& other) const {
        return add(*this, other);
    }

    // 减法
    Rational_Fr operator-(const Rational_Fr& other) const {
        return sub(*this, other);
    }

    // 乘法
    Rational_Fr operator*(const Rational_Fr& other) const {
        return mul(*this, other);
    }

    // 除法
    Rational_Fr operator/(const Rational_Fr& other) const {
        return div(*this, other);
    }

    // 相等性
    bool operator==(const Rational_Fr& other) const {
        return eq(*this, other);
    }
    
    friend std::ostream& operator<<(std::ostream& os, const Rational_Fr& r) {
        os << r.numerator.getStr(16) << "/" << r.denominator.getStr(16);
        return os;
    }
    
};

#endif // RATIONAL_FR_H
