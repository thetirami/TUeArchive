//
// Created by xuanshu on 2022/05/26.
//

#pragma once
#include "UseCase.h"

class UseCase;
class Solver {
private:
public:
    virtual void simulationStep(UseCase* uc) = 0;
};
