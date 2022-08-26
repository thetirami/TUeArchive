//
// Created by xuanshu on 2022/06/16.
//

#pragma once

#include "force/Force.h"


class CollisionForce : public Force {
private:
    Particle* _rBody1;
    Particle* _rBody2;
    float _threshold = 0.0f;
    float _epsilon = 0.2f;
public:
    CollisionForce(Particle* p1, Particle* p2, float threshold, float epsilon);
    std::vector<Particle*> p() override {
        std::vector<Particle*> res {_rBody1, _rBody2};
        return res;
    };
    std::map<int, std::map<int, float>> dx() override {
        return {};
    };
    Eigen::MatrixXf dv() override {
        return {};
    };
    void draw() override {};
    void apply() override {
        std::vector<Eigen::Vector2f> rb1Corner = _rBody1->boundBox();
        for (const auto &corner : rb1Corner) {
            if (colliding(corner, _rBody1, _rBody2)) {
                collision(corner, _rBody1, _rBody2);
                if (containing(corner, _rBody1, _rBody2))
                    collision(corner, _rBody1, _rBody2);
            }
        }
        std::vector<Eigen::Vector2f> rb2Corner = _rBody2->boundBox();
        for (const auto &corner : rb2Corner) {
            if (colliding(corner, _rBody2, _rBody1)) {
                collision(corner, _rBody2, _rBody1);
                if (containing(corner, _rBody2, _rBody1))
                    collision(corner, _rBody2, _rBody1);
            }
        }
    };
    static bool containing(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2);
    bool colliding(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2) const;
    void collision(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2) const;
};

