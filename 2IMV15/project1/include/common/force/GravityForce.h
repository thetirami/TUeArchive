#pragma once

#include "force/Force.h"

class GravityForce : public Force {
private:
    Particle* const _p;
    Vec2f g = Vec2f(0.0f, -9.8f);
//    Vec2f g = Vec2f(0.0f, -0.0f);

public:
    explicit GravityForce(Particle* p);
    std::vector<Particle*> p() override {
        return {_p};
    }
    std::map<int, std::map<int, float>> dx() override {
        return {};
    }
    Eigen::MatrixXf dv() override {
        return {};
    }
    void apply() override {
        _p->updateF(_p->m() * g);
    }
    void draw() override {
    }
};
