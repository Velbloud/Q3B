#ifndef UNCONSTRAINEDVARIABLESIMPLIFIER_H
#define UNCONSTRAINEDVARIABLESIMPLIFIER_H

#include "z3++.h"
#include <map>
#include <vector>
#include <string>
#include <tuple>
#include <unordered_map>

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum MulReplacementMode { MUL, SHIFT };
enum MulReplacement { ODD, LINEAR, ALL };

typedef std::tuple<std::string, BoundType, int> BoundVar;

namespace std
{
  template<>
    struct hash<z3::expr>
    {
      size_t operator() (const z3::expr& e) const
      {
	return e.hash();
      }
    };

  template<>
    struct hash<std::pair<z3::expr, bool>>
    {
      size_t operator () (const std::pair<z3::expr,bool> &p) const {
	auto h1 = p.first.hash();
	auto h2 = std::hash<bool>{}(p.second);

	return h1 ^ h2;
      }
    };

  template<>
    struct hash<BoundVar>
    {
      size_t operator() (const BoundVar& p) const
      {
	auto h1 = std::hash<std::string>{}(std::get<0>(p));
	auto h2 = 1 + std::get<1>(p);
	auto h3 = std::get<2>(p);

	return h1 ^ h2 ^ h3;
      }
    };

   template<>
     struct hash<std::vector<BoundVar>>
    {
      std::size_t operator()(const std::vector<BoundVar>& vec) const {
	std::size_t seed = vec.size();
	for(auto& i : vec) {
	  seed ^= std::hash<BoundVar>{}(i) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
	}
	return seed;
      }
    };

  template<>
    struct hash<std::pair<z3::expr, std::vector<BoundVar>>>
    {
      size_t operator () (const std::pair<z3::expr, std::vector<BoundVar>> &p) const {
	auto h1 = p.first.hash();
	auto h2 = std::hash<std::vector<BoundVar>>{}(p.second);

	return h1 ^ h2;
      }
    };

  template<>
    struct hash<std::pair<z3::expr, unsigned int>>
    {
      size_t operator () (const std::pair<z3::expr, unsigned int> &p) const {
	auto h1 = p.first.hash();
	auto h2 = p.second;

	return h1 ^ h2;
      }
    };

  template<>
    struct hash<std::pair<z3::expr, const std::vector<BoundVar>*>>
    {
      size_t operator () (const std::pair<z3::expr, std::vector<BoundVar>*> &p) const {
	auto h1 = p.first.hash();
	auto h2 = (size_t)p.second;

	return h1 ^ h2;
      }
    };
}

class UnconstrainedVariableSimplifier
{
public:
    UnconstrainedVariableSimplifier(z3::context &ctx, z3::expr expr) : expression(expr)
    {
      this->context = &ctx;
    }

    void PrintUnconstrained()
    {
	std::cout << "------" << std::endl;
        bool allConstrained = true;

        for (auto &item : variableCounts)
        {
            if (item.second == 1)
            {
                allConstrained = false;
                std::cout << "Unconstrained variable: " << item.first << std::endl;
            }
        }
        if (allConstrained) std::cout << "All variables constrained" << std::endl;
	std::cout << "------" << std::endl;
    }

    void SimplifyOnce()
    {
        expression = simplifyOnce(expression, {}, true);
    }

    z3::expr GetExpr() const { return expression; }

    void SimplifyIte();
    z3::expr CanonizeBoundVariables(const z3::expr&);

    void SetCountVariablesLocally(bool countVariablesLocally)
    {
	this->countVariablesLocally = countVariablesLocally;
    }

    void SetDagCounting(bool dagCounting)
    {
	this->dagCounting = dagCounting;
    }

    void SetMulReplacementMode(MulReplacementMode mulReplacementMode)
    {
	this->mulReplacementMode = mulReplacementMode;
    }

    void SetMulReplacement(MulReplacement mulReplacement)
    {
	this->mulReplacement = mulReplacement;
    }

private:
    z3::context* context;
    z3::expr expression;

    std::unordered_map<std::pair<z3::expr, bool>, std::pair<std::map<std::string, int>, std::vector<BoundVar>>> subformulaVariableCounts;
    std::unordered_map<std::pair<z3::expr, std::vector<BoundVar>>, int> subformulaMaxDeBruijnIndices;
    std::map<std::string, int> variableCounts;
    std::unordered_map<std::pair<z3::expr, std::vector<BoundVar>>, bool> subformulaAllConstrained;

    typedef std::unordered_map<z3::expr, std::pair<z3::expr, const std::vector<BoundVar>>> cacheMapType;

    cacheMapType trueSimplificationCache;
    cacheMapType falseSimplificationCache;

    std::map<std::string, int> countVariableOccurences(z3::expr, std::vector<BoundVar>&, bool);
    void addCounts(std::map<std::string, int>&, std::map<std::string, int>&);
    bool allConstrained(std::map<std::string, int>&);
    int getMaxLevel(z3::expr, const std::vector<BoundVar>&, bool);

    z3::expr simplifyOnce(z3::expr, std::vector<BoundVar>, bool);
    bool isUnconstrained(z3::expr, const std::vector<BoundVar>&) const;
    bool isVar(z3::expr) const;
    bool isBefore(z3::expr, z3::expr, const std::vector<BoundVar>&, bool);
    BoundType getBoundType(z3::expr, const std::vector<BoundVar>&);

    int getNumberOfLeadingZeroes(const z3::expr&);
    int lastBound = 0;

    bool countVariablesLocally = false;
    bool dagCounting = false;
    MulReplacementMode mulReplacementMode = MUL;
    MulReplacement mulReplacement = ALL;
    int cacheHits = 0;
};

#endif // UNCONSTRAINEDVARIABLESIMPLIFIER_H