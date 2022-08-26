#pragma once

#include "force/Force.h"

class SpringForce : public Force {
private:
    Particle* _p1;    // particle 1
    Particle* _p2;    // particle 2
    double _dist;     // rest length
    double _ks, _kd;  // spring strength constants
public:
    SpringForce(Particle *p1, Particle *p2, double dist, double ks, double kd);
    std::vector<Particle*> p() override {
        std::vector<Particle*> res {_p1, _p2};
        return res;
    }
    std::map<int, std::map<int, float>> dx() override {
        std::map<int, std::map<int, float>> res;
        Eigen::MatrixXf I = Eigen::MatrixXf::Identity(2, 2);
        Eigen::Vector2f length = _p1->pos() - _p2->pos();
        Eigen::Vector2f dl = _p1->v() - _p2->v(); // l'=velocity p1-velocity p2
        Eigen::Vector2f xij = Eigen::Vector2f(length[0], length[1]);
        Eigen::Vector2f vij = Eigen::Vector2f(dl[0], dl[1]);
        float xij_magnitude = xij.norm();
        Eigen::Vector2f xij_norm = Eigen::Vector2f(length[0] / xij_magnitude, length[1] / xij_magnitude);
//        Eigen::MatrixXf force = -_ks * ((1 - _dist / xij_magnitude) * (I - xij_norm * xij_norm.transpose()) + xij_norm * xij_norm.transpose()) - _kd * vij * ((I - xij_norm * xij_norm.transpose()) / xij_magnitude * xij_norm + xij_norm * (I - xij_norm * xij_norm.transpose()) / xij_magnitude);
        Eigen::MatrixXf force = - _ks * ((1 - _dist / xij_magnitude) * (I - xij_norm * xij_norm.transpose()) + xij_norm * xij_norm.transpose());
        for (int i = 0; i < force.rows(); i++) {
            for (int j = 0; j < force.cols(); j++) {
                res[_p1->ind()*2+i][_p2->ind()*2+j] = force(i, j);
                res[_p2->ind()*2+i][_p1->ind()*2+j] = -force(i, j);
            }
        }
        return res;
    }
    Eigen::MatrixXf dv() override {
        Eigen::Vector2f length = _p1->pos() - _p2->pos();
        Eigen::Vector2f xij = Eigen::Vector2f(length[0], length[1]);
        float xij_magnitude = xij.norm();
        Eigen::Vector2f xij_norm = Eigen::Vector2f(length[0] / xij_magnitude, length[1] / xij_magnitude);
        return _kd * xij_norm * xij_norm.transpose();
    }
    void apply() override;
    void draw() override;
};
