//
// Created by xuanshu on 2022/06/16.
//

#include "eigen/Dense"
#include "force/CollisionForce.h"


CollisionForce::CollisionForce(Particle *p1, Particle *p2, float threshold, float epsilon) :
    _rBody1(p1), _rBody2(p2), _threshold(threshold), _epsilon(epsilon) {

}

bool CollisionForce::colliding(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2) const {
    std::vector<Eigen::Vector2f> edgeVec = rb2->getClosestEdge(point);
    // check if the distance from point to line close enough
    float minDist = Particle::minDistance(edgeVec[0], edgeVec[1], point);
    if (minDist > 0.02)
        return false;
    Eigen::Vector2f closestEdge = edgeVec[0] - edgeVec[1];
    Eigen::Vector2f normal = Eigen::Vector2f(closestEdge[1], -closestEdge[0]).normalized();
    Eigen::Vector2f ra = point - rb1->massCenter(), rb = point - rb2->massCenter();
    Eigen::Vector2f rv = (rb1->v() + rb1->omega() * ra) - (rb2->v() + rb2->omega() * rb);
    // Vector2f rv = (rb2->x + rb2->omega * rb) - (rb1->x - rb1->omega * rb);
    float vrel = normal.dot(rv);
    if (vrel > _threshold)
        return false;
    else
        return true;
}

bool CollisionForce::containing(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2) {
    Eigen::Vector2f e12 = rb2->boundBox(0) - rb2->boundBox(1);
    Eigen::Vector2f e14 = rb2->boundBox(0) - rb2->boundBox(3);
    Eigen::Vector2f e1i = rb2->boundBox(0) - point;
    float a = e1i.dot(e12), b = e1i.dot(e14);
    if (a > 0 && a < e12.dot(e12) && b > 0 && b < e14.dot(e14))
        return true;
    return false;
}

void CollisionForce::collision(const Eigen::Vector2f& point, Particle *rb1, Particle *rb2) const {
    std::vector<Eigen::Vector2f> edgeVec = rb2->getClosestEdge(point);
    // edge vector
    Eigen::Vector2f closestEdge = edgeVec[0] - edgeVec[1];
    Eigen::Vector2f normal = Eigen::Vector2f(closestEdge[1], -closestEdge[0]).normalized();
    Eigen::Vector2f ra = point - rb1->massCenter(), rb = point - rb2->massCenter();
    Eigen::Vector2f rv = (rb1->v() + rb1->omega() * ra) - (rb2->v() + rb2->omega() * rb);
    float vrel = normal.dot(rv), numerator = -(1 + _epsilon) * vrel;
    float term1 = 1 / rb1->m();
    float term2 = 1 / rb2->m();
    Eigen::MatrixXf raN(2, 2), rbN(2, 2), raF(2, 2), rbF(2, 2);
    raN(0, 0) = ra[0], raN(0, 1) = ra[1], raN(1, 0) = normal[0], raN(1, 1) = normal[1];
    rbN(0, 0) = rb[0], rbN(0, 1) = rb[1], rbN(1, 0) = normal[0], rbN(1, 1) = normal[1];
    float raCrossN = raN.determinant();
    float rbCrossN = rbN.determinant();
    float term3 = (raCrossN * raCrossN) * (1 / rb1->inertia());
    float term4 = (rbCrossN * rbCrossN) * (1 / rb2->inertia());
    float j = numerator / (term1 + term2 + term3 + term4);
    float scale = 3;
    Eigen::Vector2f force = scale * j * normal;
    raF(0, 0) = ra[0], raF(0, 1) = ra[1], raF(1, 0) = force[0], raF(1, 1) = force[1];
    rbF(0, 0) = rb[0], rbF(0, 1) = rb[1], rbF(1, 0) = force[0], rbF(1, 1) = force[1];
    if (std::abs(force[0]) < 20)
        force[0] *= 45;
    else
        force[0] *= 15;
    if (std::abs(force[1]) < 20)
        force[1] *= 45;
    else
        force[1] *= 15;
    rb1->updateF( force * 8);
    rb2->updateF(-force * 8);
    rb1->updateTorque( (1 / rb1->inertia()) / 100 * raF.determinant());
    rb2->updateTorque(-(1 / rb2->inertia()) / 100 * rbF.determinant());
}
