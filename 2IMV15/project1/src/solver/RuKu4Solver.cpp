//
// Created by xuanshu on 2022/05/26.
//

#include "solver/RuKu4Solver.h"

RuKu4Sovler::RuKu4Sovler() = default;

void RuKu4Sovler::simulationStep(UseCase *uc) {
    // Get the old state
    Eigen::VectorXf oldState = uc->getState();
    float oldTime = uc->t();
    //Evaluate derivative
    Eigen::VectorXf stateDeriv = uc->aParticle();
    //Calculate k1
    Eigen::VectorXf k1 = uc->dt() * stateDeriv;
    //Get midpoint and Calculate k2
    Eigen::VectorXf newState = oldState + k1 / 2;
    uc->setState(newState, oldTime + uc->dt() / 2);
    stateDeriv = uc->aParticle();
    Eigen::VectorXf k2 = uc->dt() * stateDeriv;
    //Get midpoint and Calculate k3
    newState = oldState + k2 / 2;
    uc->setState(newState, oldTime + uc->dt() / 2);
    stateDeriv = uc->aParticle();
    Eigen::VectorXf k3 = uc->dt() * stateDeriv;
    //Get midpoint and Calculate k4
    newState = oldState + k3;
    uc->setState(newState, oldTime + uc->dt());
    stateDeriv = uc->aParticle();
    Eigen::VectorXf k4 = uc->dt() * stateDeriv;
    //Final state generation
    newState = oldState + 1.0f / 6.0f * k1 + 1.0f / 3.0f * k2 + 1.0f / 3.0f * k3 + 1.0f / 6.0f * k4;
    if (uc->wall())
        newState = uc->wallCollision(newState);
    // final state
    uc->setState(newState, oldTime + uc->dt());
}
