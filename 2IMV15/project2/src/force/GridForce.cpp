//
// Created by xuanshu on 2022/06/17.
//
#include "force/GridForce.h"
#include <utility>

GridForce::GridForce(std::vector<Particle*> particle, Fluid* fluid, int scale)
        :  _particle(std::move(particle)), _fluid(fluid),  _scale(scale) {
}

