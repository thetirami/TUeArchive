#include "constraint/FixedConstraint.h"
#include <GL/glut.h>

#include <cmath>
#include <utility>

#define PI 3.1415926535897932384626433832795


FixedConstraint::FixedConstraint(Particle *p, Eigen::Vector2f center) :
    _p(p), _center(std::move(center)) {

}

static void draw_circle(const Eigen::Vector2f& vect, float radius) {
    glBegin(GL_LINE_LOOP);
    glColor3f(0.0,1.0,0.0);
    for (int i = 0; i < 360; i = i + 18) {
        float degInRad = i * PI / 180.0f;
        glVertex2f(vect[0] + std::cos(degInRad) * radius, vect[1] + std::sin(degInRad) * radius);
    }
    glEnd();
}

void FixedConstraint::draw() {
    draw_circle(_center, 0.01);
    glBegin(GL_LINES);
    glColor3f(0.7,0.7,0.0);
    glVertex2f(_p->pos(0), _p->pos(1));
    glVertex2f(_center[0], _center[1]);
    glEnd();
}
