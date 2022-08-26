
#include <vector>
#include <cstdlib>
#include <cstdio>
#include <GL/glut.h>

#include "imageio.h"
#include "Particle.h"
#include "DemoConstructor.h"

#include "force/MouseForce.h"
#include "solver/EulerSolver.h"
#include "solver/MidPointSolver.h"
#include "solver/RuKu4Solver.h"


/* global variables */

static int N;
static float dt, d;
static int dsim;
static int dump_frames;
static int frame_number;

// UseCase
UseCase* useCase;
DemoConstructor* demoConstructor;
MouseForce* mouseForce;
float externalF;

static int win_id;
static int win_x, win_y;
static int mouse_down[3];
static int mouse_release[3];
static int mouse_shiftclick[3];
static int omx, omy, mx, my;
static int hmx, hmy;

//static SpringForce * delete_this_dummy_spring = NULL;
//static RodConstraint * delete_this_dummy_rod = NULL;
//static CircularWireConstraint * delete_this_dummy_wire = NULL;


/*
----------------------------------------------------------------------
free/clear/allocate simulation data
----------------------------------------------------------------------
*/

static void free_data() {
    useCase->clean();
}

static void clear_data() {
    useCase->reset();
}

static void init_system() {
    useCase = new UseCase(new EulerSolver(EulerSolver::SEMI));
    demoConstructor = new DemoConstructor();
}

/*
----------------------------------------------------------------------
OpenGL specific drawing routines
----------------------------------------------------------------------
*/

static void pre_display() {
	glViewport ( 0, 0, win_x, win_y );
	glMatrixMode ( GL_PROJECTION );
	glLoadIdentity ();
	gluOrtho2D ( -1.0, 1.0, -1.0, 1.0 );
	glClearColor ( 0.0f, 0.0f, 0.0f, 1.0f );
	glClear ( GL_COLOR_BUFFER_BIT );
}

static void post_display() {
	// Write frames if necessary.
	if (dump_frames) {
		const int FRAME_INTERVAL = 4;
		if ((frame_number % FRAME_INTERVAL) == 0) {
			const unsigned int w = glutGet(GLUT_WINDOW_WIDTH);
			const unsigned int h = glutGet(GLUT_WINDOW_HEIGHT);
			unsigned char * buffer = (unsigned char *) malloc(w * h * 4 * sizeof(unsigned char));
			if (!buffer)
				exit(-1);
			// glRasterPos2i(0, 0);
			glReadPixels(0, 0, w, h, GL_RGBA, GL_UNSIGNED_BYTE, buffer);
			static char filename[80];
			sprintf(filename, "../snapshots/img%.5i.png", frame_number / FRAME_INTERVAL);
			printf("Dumped %s.\n", filename);
			saveImageRGBA(filename, buffer, w, h);
			free(buffer);
		}
	}
	frame_number++;
	glutSwapBuffers ();
}

static void draw_particles() {
	useCase->drawP();
}

static void draw_forces() {
    useCase->drawF();
}

static void draw_constraints() {
    useCase->drawC();
}

/*
----------------------------------------------------------------------
relates mouse movements to particle toy construction
----------------------------------------------------------------------
*/

static void get_from_UI () {
	int i, j;
	// int size, flag;
	int hi, hj;
	// float x, y;
	if ( !mouse_down[0] && !mouse_down[2] && !mouse_release[0] 
	&& !mouse_shiftclick[0] && !mouse_shiftclick[2] ) return;

	i = (int)((       mx /(float)win_x)*N);
	j = (int)(((win_y-my)/(float)win_y)*N);

	if ( i<1 || i>N || j<1 || j>N ) return;

	if ( mouse_down[0] ) {

	}

	if ( mouse_down[2] ) {
	}

	hi = (int)((       hmx /(float)win_x)*N);
	hj = (int)(((win_y-hmy)/(float)win_y)*N);

	if( mouse_release[0] ) {
	}

	omx = mx;
	omy = my;
}

static void remap_GUI() {
    for (auto p : useCase->p()) {
        p->setPos(p->initPos());
    }
//	int ii, size = pVector.size();
//	for(ii=0; ii<size; ii++)
//	{
//		pVector[ii]->setPos(pVector[ii]->initPos());
//		// pVector[ii]->m_Position[0] = pVector[ii]->m_ConstructPos[0];
//		// pVector[ii]->m_Position[1] = pVector[ii]->m_ConstructPos[1];
//	}
}

/*
----------------------------------------------------------------------
GLUT callback routines
----------------------------------------------------------------------
*/

static void key_func(unsigned char key, int x, int y) {
	switch (key) {
        case '0':
            if (dsim)
                dsim = !dsim;
            init_system();
            demoConstructor->DummyToy(useCase);
            break;
        case '1':
            if (dsim)
                dsim = !dsim;
            init_system();
            externalF = 0.001f;
            demoConstructor->Cloth2D(useCase);
            break;
        case '2':
            if (dsim)
                dsim = !dsim;
            init_system();
            externalF = 0.001f;
            useCase->setDt(0.0001f);
            demoConstructor->AngularSpring(useCase);
            break;
        case '3':
            if (dsim)
                dsim = !dsim;
            init_system();
            externalF = 0.001f;
            useCase->setDt(0.0001f);
            demoConstructor->Hair(useCase);
            break;
        case 'e':
        case 'E':
            useCase->setSolver(new EulerSolver(EulerSolver::EXPLICIT));
            printf("Switched to explicit Euler solver...\n");
            break;
        case 's':
        case 'S':
            useCase->setSolver(new EulerSolver(EulerSolver::SEMI));
            printf("Switched to semi Euler solver...\n");
            break;
        case 'i':
        case 'I':
            useCase->setSolver(new EulerSolver(EulerSolver::IMPLICIT));
            printf("Switched to implicit solver...\n");
            break;
        case 'm':
        case 'M':
            useCase->setSolver(new MidPointSolver());
            printf("Switched to mid-point solver...\n");
            break;
        case 'r':
        case 'R':
            useCase->setSolver(new RuKu4Sovler());
            printf("Switched to Runge-Kutta 4 solver...\n");
            break;
        case 'c':
        case 'C':
            clear_data ();
            break;

        case 'd':
        case 'D':
            dump_frames = !dump_frames;
            break;

        case 'q':
        case 'Q':
            free_data();
            exit(0);
            break;

        case ' ':
            dsim = !dsim;
            if (dsim)
                useCase->reset();
            break;
        default:
            break;
	}
}

static void mouse_func(int button, int state, int x, int y) {
	omx = mx = x;
	omx = my = y;

	if(!mouse_down[0]){hmx=x; hmy=y;}
	if(mouse_down[button]) mouse_release[button] = state == GLUT_UP;
	if(mouse_down[button]) mouse_shiftclick[button] = glutGetModifiers()==GLUT_ACTIVE_SHIFT;
	mouse_down[button] = state == GLUT_DOWN;

    if (state == GLUT_UP) {
        mouseForce->active(false);
    } else {
        int mouse_x = x - int(win_x/2);
        int mouse_y = int(win_y/2) - y;
        Particle* closestP = nullptr;
        double closestDist = 100000;
        for (int i = 0; i < useCase->p().size(); i++) {
            Vec2f position = useCase->p(i)->pos();
            double distance = sqrt(pow(mouse_x - (position[0]*(win_x/2)),2) + pow(mouse_y - (position[1]*(win_y/2)),2));
            if (distance < closestDist) {
                closestDist = distance;
                closestP = useCase->p(i);
            }
        }
        if (closestP != nullptr) {
            mouseForce = new MouseForce(closestP, Vec2f(0.0f,0.0f), externalF);
            useCase->addForce(mouseForce);
        }
    }
}

static void motion_func(int x, int y) {
    mx = x - int(win_x/2);
    my = int(win_y/2) - y;
    if (mouseForce != nullptr) {
        Vec2f position = mouseForce->pp()->pos();
        mouseForce->setDirection(3.0f * Vec2f(mx-position[0]*(win_x/2), my-position[1]*(win_y/2)));
    }
}

static void reshape_func(int width, int height) {
	glutSetWindow ( win_id );
	glutReshapeWindow ( width, height );
	win_x = width;
	win_y = height;
}

static void idle_func() {
	if (dsim) {
        useCase->simulationStep();
    } else {
        get_from_UI();
        remap_GUI();
    }
	glutSetWindow(win_id);
	glutPostRedisplay();
}

static void display_func() {
	pre_display ();
	draw_forces();
	draw_constraints();
	draw_particles();
	post_display ();
}


/*
----------------------------------------------------------------------
open_glut_window --- open a glut compatible window and set callbacks
----------------------------------------------------------------------
*/

static void open_glut_window(){
	glutInitDisplayMode ( GLUT_RGBA | GLUT_DOUBLE );
	glutInitWindowPosition ( 0, 0 );
	glutInitWindowSize ( win_x, win_y );
	win_id = glutCreateWindow ( "Particletoys!" );
	glClearColor ( 0.0f, 0.0f, 0.0f, 1.0f );
	glClear ( GL_COLOR_BUFFER_BIT );
	glutSwapBuffers ();
	glClear ( GL_COLOR_BUFFER_BIT );
	glutSwapBuffers ();
	glEnable(GL_LINE_SMOOTH);
	glEnable(GL_POLYGON_SMOOTH);
	pre_display ();
	glutKeyboardFunc ( key_func );
	glutMouseFunc ( mouse_func );
	glutMotionFunc ( motion_func );
	glutReshapeFunc ( reshape_func );
	glutIdleFunc ( idle_func );
	glutDisplayFunc ( display_func );
}


/*
----------------------------------------------------------------------
main --- main routine
----------------------------------------------------------------------
*/

int main(int argc, char ** argv) {
	glutInit(&argc, argv);
	if (argc == 1) {
		N = 64;
		dt = 0.1f;
		d = 5.f;
//		fprintf(stderr, "Using defaults : N=%d dt=%g d=%g\n", N, dt, d);
	} else {
		N = atoi(argv[1]);
		dt = atof(argv[2]);
		d = atof(argv[3]);
	}

	printf("\n\nHow to use this application:\n\n");
	printf("\t Toggle construction/simulation display with the spacebar key\n");
	printf("\t Dump frames by pressing the 'd' key\n");
    printf("\t Quit by pressing the 'q' key\n\n");
    printf("\t [Press 1] --- 2D Cloth demo\n");
    printf("\t [Press 2] --- Angular springs demo\n");
    printf("\t [Press 3] --- Hairs demo\n\n");
    printf("\t [Press e] --- Switch to Explicit Euler Solver\n");
    printf("\t [Press s] --- Switch to Semi Euler Solver (by DEFAULT)\n");
    printf("\t [Press i] --- Switch to Implicit Solver\n");
    printf("\t [Press m] --- Switch to Mid-point Solver\n");
    printf("\t [Press r] --- Switch to Runge-Kutta 4 Solver\n\n");

	dsim = 0;
	dump_frames = 0;
	frame_number = 0;
	init_system();

	win_x = 768;
	win_y = 768;
	open_glut_window();

	glutMainLoop();
	exit(0);
}

