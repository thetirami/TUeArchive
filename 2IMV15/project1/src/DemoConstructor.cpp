//
// Created by xuanshu on 2022/05/27.
//
#include "DemoConstructor.h"
#include "force/AngularSpringForce.h"
#include "force/GravityForce.h"
#include "force/SpringForce.h"
#include "constraint/FixedConstraint.h"
#include "constraint/RodConstraint.h"


void DemoConstructor::DummyToy(UseCase *uc) {
    const double dist = 0.2;
    const Vec2f center(0.0, 0.0);
    const Vec2f offset(dist, 0.0);

    uc->addParticle(new Particle(center + offset, 10.0f, 0));
    uc->addParticle(new Particle(center + 2 * offset, 10.0f, 1));
    uc->addParticle(new Particle(center + 3 * offset, 10.0f, 2));
    uc->addParticle(new Particle(center + 4 * offset, 10.0f, 3));
    uc->addForce(new SpringForce(uc->p(0), uc->p(1), dist/2, 10.f, 1.0f));
    uc->addForce(new SpringForce(uc->p(2), uc->p(3), dist/2, 10.f, 1.0f));
    uc->addConstraint(new RodConstraint(uc->p(1), uc->p(2), dist));
}

void DemoConstructor::Cloth2D(UseCase *uc) {
    const int xSize = 5, ySize = 5;
    const float dist = 0.3;
    const float m = 0.02f;
    int index = 0;

    for (int j = 0; j < ySize; j++) {
        for (int i = 0; i < xSize; i++) {
            if (j == 0) {
                Vec2f pos = Vec2f(-0.6f + i * dist + (2-i)*0.02, 0.6f - j * dist);
                uc->addParticle(new Particle(pos, m, index));
                uc->addConstraint(new FixedConstraint(uc->p(index), pos));
            } else {
                uc->addParticle(new Particle(Vec2f(-0.6f + i * dist, 0.6f - j * dist), m, index));
            }
            uc->addForce(new GravityForce(uc->p(index)));
            index++;
        }
    }

    float ks = 20.0f;
    float kd = 0.5f;
//    sys->wall=true;
//    sys->addForce(new DragForce(sys->particles, 0.3f));
//    sys->wall=true;
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

void DemoConstructor::AngularSpring(UseCase *uc) {
    Vec2f initUpperPos = Vec2f(0, 0.2);
    uc->addParticle(new Particle(initUpperPos, 0.005, 0));
    uc->addParticle(new Particle(Vec2f(-0.1, 0), 0.02, 1));
    uc->addParticle(new Particle(Vec2f(0, -0.2), 0.005, 2));

    float ks = 20.0f;
    float kd = 0.5f;

    uc->addForce(new SpringForce(uc->p(0), uc->p(1), 0.25, ks, kd));
    uc->addForce(new SpringForce(uc->p(1), uc->p(2), 0.25, ks, kd));
    for (auto p : uc->p()) {
        uc->addForce(new GravityForce(p));
    }
    uc->addForce(new AngularSpringForce(uc->p(0), uc->p(1), uc->p(2), 80, 8, kd));
    uc->addConstraint(new FixedConstraint(uc->p(0), initUpperPos));
}

void DemoConstructor::Hair(UseCase *uc) {
    Vec2f initUpperPos = Vec2f(0, 0.4);
    uc->addParticle(new Particle(initUpperPos, 0.005, 0));
    uc->addParticle(new Particle(Vec2f(-0.1, 0.3), 0.005, 1));
    uc->addParticle(new Particle(Vec2f(0, 0.2), 0.005, 2));
    uc->addParticle(new Particle(Vec2f(-0.1, 0.1), 0.005, 3));
    uc->addParticle(new Particle(Vec2f(0, 0), 0.005, 4));
    uc->addParticle(new Particle(Vec2f(-0.1, -0.1), 0.005, 5));
    uc->addParticle(new Particle(Vec2f(0, -0.2), 0.005, 6));
    uc->addParticle(new Particle(Vec2f(-0.1, -0.3), 0.005, 7));
    uc->addParticle(new Particle(Vec2f(0, -0.4), 0.005, 8));

    float ks = 20.0f;
    float kd = 0.5f;

    for (auto i = 0; i < uc->p().size()-1; i++) {
        assert(i+1 <= 8);
        uc->addForce(new SpringForce(uc->p(i), uc->p(i+1), 0.2, ks, kd));
    }
    for (auto p : uc->p()) {
        uc->addForce(new GravityForce(p));
    }
    for (auto i = 0; i < uc->p().size()-1-1; i++) {
        assert(i+2 <= 8);
        uc->addForce(new AngularSpringForce(uc->p(i), uc->p(i+1), uc->p(i+2), 80, 8, kd));
    }
    uc->addConstraint(new FixedConstraint(uc->p(0), initUpperPos));
}


