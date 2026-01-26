FROM minizinc/minizinc:2.9.5-alpine

# Install system build tools for python
RUN apk update && apk add --no-cache \
        python3=3.12.12-r0 \
        py3-pip \
        python3-dev \
        build-base \
        cmake \
        git

# Create and activate a py venv
WORKDIR /cdmo
RUN python3 -m venv /venv
ENV PATH="/venv/bin:$PATH"

# Upgrade pip/setuptools/wheel
RUN pip install --upgrade pip setuptools wheel

# Copy & install dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy source code
COPY ./source .

CMD ["/bin/bash"]
