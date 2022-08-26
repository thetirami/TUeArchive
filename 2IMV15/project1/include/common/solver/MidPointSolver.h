#pragma once

#include "Solver.h"

class MidPointSolver : public Solver {
private:
public:
    MidPointSolver();
    void simulationStep(UseCase* uc) override;
};
