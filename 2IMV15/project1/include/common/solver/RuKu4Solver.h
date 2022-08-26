#pragma once

#include "Solver.h"

class RuKu4Sovler : public Solver {
private:
public:
    RuKu4Sovler();
    void simulationStep(UseCase* uc) override;
};