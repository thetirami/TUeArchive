//
// Created by xuanshu on 2022/05/26.
//

#include "solver/EulerSolver.h"


EulerSolver::EulerSolver(EulerSolver::TYPE type) : _type(type) {

}

void EulerSolver::simulationStep(UseCase* uc) {
    switch (_type) {
        case SEMI:
            semiSolver(uc);
    }
}

void EulerSolver::semiSolver(UseCase* uc) {
    float h = uc->dt();
    Eigen::VectorXf prevPState = uc->getPState();
    Eigen::VectorXf prevRPState = uc->getRPState();
    Eigen::VectorXf dPState = uc->aParticle();
    Eigen::VectorXf dRPState = uc->aRParticle();
    Eigen::VectorXf currPState = prevPState + h * dPState;
    Eigen::VectorXf currRPState = prevRPState + h * dRPState;
    for (int i = 0; i < currPState.size(); i += 4) {
        currPState[i + 0] = prevPState[i + 0] + h * currPState[i + 2];
        currPState[i + 1] = prevPState[i + 1] + h * currPState[i + 3];
    }
    for (int i = 0; i < currRPState.size(); i += 8) {
        currRPState[i + 0] = prevRPState[i + 0] + h * (currRPState[i + 3] / prevRPState[i + 6]);
        currRPState[i + 1] = prevRPState[i + 1] + h * (currRPState[i + 4] / prevRPState[i + 6]);
        currRPState[i + 2] = prevRPState[i + 2] + h * (currRPState[i + 5] / prevRPState[i + 7]);
    }
    if (uc->wall()) {
        currPState = uc->wallPCollision(currPState);
        currRPState = uc->wallRPCollision(currRPState);
    }
    uc->setPState(currPState, uc->t() + h);
    uc->setRPState(currRPState, uc->t() + h);
}

