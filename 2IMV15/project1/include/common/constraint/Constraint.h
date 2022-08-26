//
// Created by xuanshu on 2022/05/26.
//

#ifndef UNIFIED_MAKEFILE_PROJECT1_CONSTRAINT_H
#define UNIFIED_MAKEFILE_PROJECT1_CONSTRAINT_H

#include <gfx/vec2.h>
#include "Particle.h"

class Constraint {
private:
public:
    virtual void draw() = 0;
    virtual std::vector<Particle*> p() = 0;
    virtual float C() = 0;
    virtual float legalV() = 0;
    virtual std::vector<Vec2f> jacobian() = 0;
    virtual std::vector<Vec2f> dJacobian() = 0;
};

#endif //UNIFIED_MAKEFILE_PROJECT1_CONSTRAINT_H
