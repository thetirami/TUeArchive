//
// Created by xuanshu on 2022/06/17.
//

#include "Force.h"
#include "Fluid.h"
#include "Particle.h"
#include <map>

class GridForce : public Force {
private:
    std::vector<Particle*> _particle;
    Fluid* _fluid;
    int _scale;
public:
    GridForce(std::vector<Particle*> particle, Fluid* fluid, int scale);
    std::vector<Particle*> p() override {
        return _particle;
    }
    void apply() override {
        if (isActive()) {
            for (Particle *rb : _particle) {
                std::vector<Eigen::Vector4f> grids = rb->boundGrid(128);
                // cout<<rb->torque<<endl;
                for (auto & grid : grids) {
                    // use v,F of the grids that edges pass through to update
                    float u = _fluid->getXVelocity((int)grid[0], (int)grid[1]);
                    float v = _fluid->getYVelocity((int)grid[0], (int)grid[1]);
                    float density = _fluid->getDensity((int)grid[0], (int)grid[1]);
                    Eigen::Vector2f CenterToGrid = Eigen::Vector2f(grid[2], grid[3]);

                    // Find which edge is current grid allocated on
                    std::vector<Eigen::Vector2f> edges;
                    std::vector<Eigen::Vector2f> normals;
                    for (int j = 0; j < rb->boundBox().size(); j++) {
                        edges.emplace_back(rb->boundBox((j + 1) % (rb->boundBox().size())) - rb->boundBox(j % (rb->boundBox().size())));
                        normals.emplace_back(edges[j][1], -edges[j][0]);
                    }
                    Eigen::Vector2f on_edge;
                    Eigen::Vector2f normal;
                    for (int j = 0; j < normals.size(); j++) {
                        if (CenterToGrid.dot(normals[j]) / (CenterToGrid.norm() * normals[j].norm()) <= -sqrt(2) / 2) {
                            on_edge = edges[j];
                            normal = normals[j].normalized();
                        }
                    }
                    float projectedVelocity = (u * on_edge[1] - on_edge[0] * v) / on_edge.norm();
                    Eigen::Vector2f localVelocity = projectedVelocity * normal;
                    rb->updateF(-localVelocity * 1000);
                    rb->updateTorque(-CenterToGrid.dot(Eigen::Vector2f(u, v)) * _scale); // torque = L*v
                }
            }
        }
    }
    std::map<int, std::map<int, float>> dx() override {
        return {};
    };
    Eigen::MatrixXf dv() override {
        return {};
    };
    void draw() override {

    };
};

