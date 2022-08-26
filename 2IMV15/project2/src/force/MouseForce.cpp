#include "force/MouseForce.h"

#include <utility>


MouseForce::MouseForce(Particle *p, Eigen::Vector2f direction, float f) :
    _p(p), _direction(std::move(direction)), _f(f) {

}
