//
// Created by xuanshu on 2022/05/26.
//

#include "solver/MidPointSolver.h"

MidPointSolver::MidPointSolver() = default;

void MidPointSolver::simulationStep(UseCase *uc) {
    // Get the initial state
    Eigen::VectorXf oldState = uc->getState();
    Eigen::VectorXf stateDeriv = uc->aParticle();
    // Compute the halfway point
    Eigen::VectorXf midPointState = oldState + uc->dt() * 0.5f * stateDeriv;
    uc->setState(midPointState, uc->t() + uc->dt());
    stateDeriv = uc->aParticle();
    Eigen::VectorXf newState = oldState + uc->dt() * stateDeriv;
    if (uc->wall())
        newState = uc->wallCollision(newState);
    uc->setState(newState, uc->t() + uc->dt());
}
