#pragma once

#include "force/Force.h"

class GravityForce : public Force {
private:
    Particle* const _p;
    Eigen::Vector2f _g = Eigen::Vector2f(0.0f, -9.8f);

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
        if (isActive()) {
            _p->updateF(_p->m() * _g);
        }
    }
    void draw() override {
    }
};
