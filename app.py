from flask import Flask, render_template, request, send_from_directory
from datetime import datetime
from parser_util.parser import *
from sat_solver.sat_engine import *
import os

app = Flask(__name__, static_folder='./assets')


@app.route('/')
def homepage():
    the_time = datetime.now().strftime("%A, %d %b %Y %l:%M %p")
    cnf, variables, phi = parse('(p3->p2)')
    return render_template('./index.html')


@app.route('/credits')
def credits():
    return render_template('./credits.html')


@app.route('/tseytin', methods=['POST'])
def tseytin():
    # call to server
    data = str(request.form['formula'])
    try:
        result = parse(data)[0]
    except:
        result = "ERROR - bad input formula syntax"
    return render_template('./index.html', got=result)


@app.route('/sat_solve', methods=['POST'])
def sat_solve():
    # call to server
    data = str(request.form['formula'])
    try:
        result = 'SAT' if solve_sat(data)[0] else 'UNSAT'
    except:
        result = "ERROR - bad input formula syntax"
    return render_template('./index.html', sat_unsat=result)


@app.route('/favicon.ico')
def favicon():
    return send_from_directory(os.path.join(app.root_path, 'assets'),
                               'favicon.ico', mimetype='image/vnd.microsoft.icon')


@app.errorhandler(404)
def page_not_found(e):
    # note that we set the 404 status explicitly
    return render_template('404.html'), 404


if __name__ == '__main__':
    app.run(debug=True, use_reloader=True)
