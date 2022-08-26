#include "constraint/CircularWireConstraint.h"
#include <GL/glut.h>

#define PI 3.1415926535897932384626433832795

static void draw_circle(const Vec2f & vect, float radius) {
	glBegin(GL_LINE_LOOP);
	glColor3f(0.0,1.0,0.0); 
	for (int i=0; i<360; i=i+18) {
		float degInRad = i*PI/180;
		glVertex2f(vect[0]+cos(degInRad)*radius,vect[1]+sin(degInRad)*radius);
	}
	glEnd();
}

CircularWireConstraint::CircularWireConstraint(Particle *p, const Vec2f & center, double radius) :
	_p(p), _center(center), _radius(radius) {

}

void CircularWireConstraint::draw() {
	draw_circle(_center, _radius);
    glBegin(GL_LINES);
    glColor3f(0.7,0.7,0.0);
    glVertex2f(_p->pos(0), _p->pos(1));
    glVertex2f(_center[0], _center[1]);
    glEnd();
}
