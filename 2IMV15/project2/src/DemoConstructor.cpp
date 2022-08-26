//
// Created by xuanshu on 2022/05/27.
//
#include "DemoConstructor.h"
#include "force/GravityForce.h"
#include "force/SpringForce.h"
#include "force/CollisionForce.h"
#include "force/GridForce.h"
#include "constraint/FixedConstraint.h"
#include "constraint/RodConstraint.h"


void DemoConstructor::DummyToy(UseCase *uc) {
}

void DemoConstructor::FixedObject(UseCase *uc, Fluid *fluid) {
    uc->addRigidParticle(new Particle(Eigen::Vector2f(-0.2f, 0.2f), 500.0f, 0, FIX));
    uc->addRigidForce(new GridForce(uc->rp(), fluid, 1000));
}

void DemoConstructor::MovingSolid(UseCase *uc, Fluid *fluid) {
    uc->addRigidParticle(new Particle(Eigen::Vector2f(-0.2f, 0.2f), 5.0f, 0, MOVING));
    uc->addRigidForce(new GridForce(uc->rp(), fluid, 1000));
}

void DemoConstructor::MovingRigid(UseCase *uc, Fluid *fluid) {
    uc->addRigidParticle(new Particle(Eigen::Vector2f(-0.2f, 0.2f), 5.0f, 0, RIGID));
    uc->addRigidForce(new GridForce(uc->rp(), fluid, 1000));
}


void DemoConstructor::Collision2R(UseCase *uc, Fluid *fluid) {
    uc->addRigidParticle(new Particle(Eigen::Vector2f(-0.2f, 0.2f), 5.0f, 0, RIGID));
    uc->addRigidParticle(new Particle(Eigen::Vector2f(0.5f, -0.4f), 5.0f, 0, RIGID));
    uc->addRigidForce(new GridForce(uc->rp(), fluid, 1000));
    uc->addRigidForce(new CollisionForce(uc->rp(0), uc->rp(1), 20, 0.9));
}

void DemoConstructor::Cloth2D(UseCase *uc) {
    const int xSize = 5, ySize = 5;
    const float dist = 0.3;
    const float m = 0.02f;
    int index = 0;
    for (int j = 0; j < ySize; j++) {
        for (int i = 0; i < xSize; i++) {
            uc->addParticle(new Particle(Eigen::Vector2f(-0.6f + i * dist, 0.6f - j * dist), m, index, NORMAL));
            index++;
        }
    }
    float ks = 500.0f;
    float kd = 0.005f;
    for (int j = 0; j < ySize; j++) { // right, left
        for (int i = 0; i < xSize - 1; i++) {
            uc->addForce(new SpringForce(uc->p(i + j * xSize), uc->p(i + 1 + j * xSize), dist, 0.1, kd));
        }
    }
    for (int j = 0; j < ySize - 1; j++) { // up, down
        for (int i = 0; i < xSize; i++) {
            uc->addForce(new SpringForce(uc->p(i + j * xSize), uc->p(i + (j + 1) * xSize), dist, ks, kd));
        }
    }
    for (int j = 0; j < ySize - 1; j++) { // diagonal
        for (int i = 0; i < xSize - 1; i++) {
            uc->addForce(new SpringForce(uc->p(i + j * xSize), uc->p(i + 1 + (j + 1) * xSize), sqrt(pow(dist,2) + pow(dist,2)), 1, kd));
        }
    }

    for (int y = 0; y < ySize - 1; y++) { //diagonal
        for (int x = 1; x < xSize; x++) {
            uc->addForce(new SpringForce(uc->p(x + y * xSize), uc->p(x - 1 + (y + 1) * xSize), sqrt(pow(dist,2) + pow(dist,2)), 1, kd));
        }
    }
}





