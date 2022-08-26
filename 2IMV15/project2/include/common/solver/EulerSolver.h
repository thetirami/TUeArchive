//
// Created by xuanshu on 2022/05/26.
//

#pragma once

#include "solver/Solver.h"

class EulerSolver : public Solver {
public:
    enum TYPE {
        SEMI
    };
    explicit EulerSolver(TYPE type);
    void simulationStep(UseCase* uc) override;
private:
    TYPE _type;
    static void semiSolver(UseCase* uc);
};
